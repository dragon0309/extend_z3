#include "util/implied_eq_partition_variants.hpp"

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <set>
#include <stdexcept>
#include <string>
#include <thread>
#include <unordered_map>
#include <utility>
#include <vector>

#include "util/fmt_duration.hpp"
#include "util/logger.hpp"

namespace util::eqpartition
{
namespace
{

using clk = std::chrono::steady_clock;

std::string sort_key(const z3::expr &term)
{
    return term.get_sort().to_string();
}

std::vector<std::vector<std::size_t>> initial_partition(
    const std::vector<z3::expr> &terms)
{
    std::map<std::string, std::vector<std::size_t>> by_sort;
    for (std::size_t i = 0; i < terms.size(); ++i)
        by_sort[sort_key(terms[i])].push_back(i);

    std::vector<std::vector<std::size_t>> blocks;
    blocks.reserve(by_sort.size());
    for (auto &[key, block] : by_sort)
        blocks.push_back(std::move(block));
    return blocks;
}

std::size_t implied_pair_count(
    const std::vector<std::vector<std::size_t>> &blocks)
{
    std::size_t count = 0;
    for (const auto &block : blocks)
        if (block.size() > 1)
            count += block.size() * (block.size() - 1) / 2;
    return count;
}

void finalize_result(Result &output,
                     std::vector<std::vector<std::size_t>> blocks)
{
    output.classes = std::move(blocks);
    std::sort(output.classes.begin(), output.classes.end(),
              [](const auto &lhs, const auto &rhs) {
                  return lhs.front() < rhs.front();
              });
    output.statistics.final_blocks = output.classes.size();
    for (const auto &block : output.classes)
    {
        if (block.size() < 2)
            continue;
        ++output.statistics.equality_classes;
        for (std::size_t i = 1; i < block.size(); ++i)
            output.proof_edges.emplace_back(block.front(), block[i]);
    }
    output.statistics.proof_edges = output.proof_edges.size();
    output.statistics.implied_pairs = implied_pair_count(output.classes);
}

std::uint64_t edge_key(std::size_t lhs, std::size_t rhs)
{
    if (lhs > rhs)
        std::swap(lhs, rhs);
    return (static_cast<std::uint64_t>(lhs) << 32) |
           static_cast<std::uint64_t>(rhs);
}

bool has_non_singleton(
    const std::vector<std::vector<std::size_t>> &blocks)
{
    return std::any_of(
        blocks.begin(), blocks.end(),
        [](const auto &block) { return block.size() > 1; });
}

std::size_t star_edge_count(
    const std::vector<std::vector<std::size_t>> &blocks)
{
    std::size_t count = 0;
    for (const auto &block : blocks)
        if (block.size() > 1)
            count += block.size() - 1;
    return count;
}

std::vector<std::size_t> representatives(
    const std::vector<std::vector<std::size_t>> &blocks,
    std::size_t term_count)
{
    std::vector<std::size_t> result(term_count, term_count);
    for (const auto &block : blocks)
    {
        if (block.empty())
            continue;
        for (std::size_t term_index : block)
            result.at(term_index) = block.front();
    }
    return result;
}

std::size_t refine_partition(
    std::vector<std::vector<std::size_t>> &blocks,
    const std::vector<z3::expr> &terms,
    const z3::model &model,
    Statistics &statistics)
{
    std::vector<std::vector<std::size_t>> refined;
    refined.reserve(blocks.size() + 1);
    std::size_t split_blocks = 0;
    for (const auto &block : blocks)
    {
        if (block.size() < 2)
        {
            if (!block.empty())
                refined.emplace_back(1, block.front());
            continue;
        }
        std::map<std::string, std::vector<std::size_t>> by_value;
        for (std::size_t term_index : block)
            by_value[model.eval(terms[term_index], true).to_string()]
                .push_back(term_index);
        if (by_value.size() > 1)
            ++split_blocks;
        for (auto &[value, part] : by_value)
            refined.push_back(std::move(part));
    }
    blocks = std::move(refined);
    if (split_blocks != 0)
    {
        ++statistics.refinements;
        statistics.blocks_split += split_blocks;
    }
    return split_blocks;
}

z3::expr fresh_bool(z3::context &context,
                    const char *prefix,
                    std::size_t &counter)
{
    const std::string name =
        std::string(prefix) + "!" + std::to_string(counter++);
    return context.bool_const(name.c_str());
}

Result run_z3_mpm(z3::context &context,
                  const std::vector<z3::expr> &constraints,
                  const std::vector<z3::expr> &terms)
{
    Result output;
    output.statistics.terms = terms.size();
    auto blocks = initial_partition(terms);
    output.statistics.initial_blocks = blocks.size();

    if (terms.empty())
    {
        output.status = Status::Complete;
        finalize_result(output, std::move(blocks));
        return output;
    }

    z3::solver solver(context);
    for (const z3::expr &constraint : constraints)
        solver.add(constraint);

    std::vector<Z3_ast> raw_terms;
    raw_terms.reserve(terms.size());
    for (const z3::expr &term : terms)
        raw_terms.push_back(static_cast<Z3_ast>(term));
    std::vector<unsigned> class_ids(terms.size(), 0);

    const auto check_started = clk::now();
    const Z3_lbool check = Z3_get_implied_equalities(
        static_cast<Z3_context>(context), static_cast<Z3_solver>(solver),
        static_cast<unsigned>(raw_terms.size()), raw_terms.data(),
        class_ids.data());
    output.statistics.check_time +=
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            clk::now() - check_started);
    // This is one public API invocation. The vendored MPM implementation runs
    // additional internal pairwise solver checks that the API does not expose.
    ++output.statistics.checks;

    if (check == Z3_L_FALSE)
    {
        ++output.statistics.unsat_checks;
        output.constraints_unsat = true;
        output.status = Status::Complete;
        finalize_result(output, std::move(blocks));
        return output;
    }
    if (check == Z3_L_UNDEF)
    {
        output.status = Status::Unknown;
        output.diagnostic = "Z3_get_implied_equalities returned unknown";
        finalize_result(output, std::move(blocks));
        return output;
    }

    ++output.statistics.sat_checks;
    std::map<std::pair<std::string, unsigned>,
             std::vector<std::size_t>> by_class;
    for (std::size_t i = 0; i < terms.size(); ++i)
        by_class[{sort_key(terms[i]), class_ids[i]}].push_back(i);
    blocks.clear();
    blocks.reserve(by_class.size());
    for (auto &[key, block] : by_class)
        blocks.push_back(std::move(block));

    output.status = Status::Complete;
    finalize_result(output, std::move(blocks));
    return output;
}

std::size_t refine_partition_with_values(
    std::vector<std::vector<std::size_t>> &blocks,
    const std::vector<std::string> &values,
    Statistics &statistics)
{
    if (values.size() != statistics.terms)
        throw std::runtime_error(
            "parallel BPR model returned the wrong number of values");

    std::vector<std::vector<std::size_t>> refined;
    refined.reserve(blocks.size() + 1);
    std::size_t split_blocks = 0;
    for (const auto &block : blocks)
    {
        if (block.size() < 2)
        {
            if (!block.empty())
                refined.emplace_back(1, block.front());
            continue;
        }
        std::map<std::string, std::vector<std::size_t>> by_value;
        for (std::size_t term_index : block)
            by_value[values.at(term_index)].push_back(term_index);
        if (by_value.size() > 1)
            ++split_blocks;
        for (auto &[value, part] : by_value)
            refined.push_back(std::move(part));
    }
    blocks = std::move(refined);
    if (split_blocks != 0)
    {
        ++statistics.refinements;
        statistics.blocks_split += split_blocks;
    }
    return split_blocks;
}

struct ParallelWorkerState
{
    std::unique_ptr<z3::context> context;
    std::vector<z3::expr> constraints;
    std::vector<z3::expr> terms;

    ParallelWorkerState(
        z3::context &source_context,
        const std::vector<z3::expr> &source_constraints,
        const std::vector<z3::expr> &source_terms)
        : context(std::make_unique<z3::context>())
    {
        constraints.reserve(source_constraints.size());
        for (const z3::expr &constraint : source_constraints)
            constraints.emplace_back(
                *context,
                Z3_translate(
                    static_cast<Z3_context>(source_context),
                    static_cast<Z3_ast>(constraint),
                    static_cast<Z3_context>(*context)));
        terms.reserve(source_terms.size());
        for (const z3::expr &term : source_terms)
            terms.emplace_back(
                *context,
                Z3_translate(
                    static_cast<Z3_context>(source_context),
                    static_cast<Z3_ast>(term),
                    static_cast<Z3_context>(*context)));
    }
};

enum class ParallelQueryOutcome
{
    Sat,
    Unsat,
    Unknown,
    Error
};

struct ParallelQueryResult
{
    ParallelQueryOutcome outcome = ParallelQueryOutcome::Error;
    std::vector<std::string> values;
    std::chrono::nanoseconds check_time{0};
    std::size_t splitter_edges = 0;
    std::string diagnostic;
};

ParallelQueryResult run_parallel_group_query(
    ParallelWorkerState &worker,
    const std::vector<std::vector<std::size_t>> &blocks,
    const std::vector<std::size_t> &block_indices,
    unsigned seed,
    unsigned timeout_ms)
{
    ParallelQueryResult output;
    try
    {
        z3::solver solver(*worker.context);
        if (timeout_ms != 0)
            solver.set("timeout", timeout_ms);
        // Workers in the same round use the same deterministic seed. Query
        // diversity comes from disjoint block groups, not a seed portfolio.
        solver.set("random_seed", seed);
        for (const z3::expr &constraint : worker.constraints)
            solver.add(constraint);

        z3::expr_vector differences(*worker.context);
        for (std::size_t block_index : block_indices)
        {
            const auto &block = blocks.at(block_index);
            if (block.size() < 2)
                throw std::runtime_error(
                    "parallel BPR assigned a singleton block");
            const std::size_t representative = block.front();
            for (std::size_t i = 1; i < block.size(); ++i)
                differences.push_back(
                    worker.terms.at(representative) !=
                    worker.terms.at(block[i]));
        }
        output.splitter_edges = differences.size();
        if (differences.empty())
            throw std::runtime_error(
                "parallel BPR worker received an empty splitter");
        solver.add(z3::mk_or(differences));

        const auto check_started = clk::now();
        const z3::check_result check = solver.check();
        output.check_time =
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - check_started);
        if (check == z3::sat)
        {
            output.outcome = ParallelQueryOutcome::Sat;
            const z3::model model = solver.get_model();
            output.values.reserve(worker.terms.size());
            for (const z3::expr &term : worker.terms)
                output.values.push_back(
                    model.eval(term, true).to_string());
        }
        else if (check == z3::unsat)
        {
            output.outcome = ParallelQueryOutcome::Unsat;
        }
        else
        {
            output.outcome = ParallelQueryOutcome::Unknown;
            output.diagnostic = solver.reason_unknown();
        }
    }
    catch (const z3::exception &ex)
    {
        output.outcome = ParallelQueryOutcome::Error;
        output.diagnostic = ex.msg();
    }
    catch (const std::exception &ex)
    {
        output.outcome = ParallelQueryOutcome::Error;
        output.diagnostic = ex.what();
    }
    return output;
}

Result run_parallel_bpr(
    z3::context &context,
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms,
    const VariantOptions &options,
    util::Logger *log)
{
    if (options.parallel_workers == 0)
        throw std::runtime_error(
            "parallel BPR requires at least one worker");

    Result output;
    output.statistics.terms = terms.size();
    auto blocks = initial_partition(terms);
    output.statistics.initial_blocks = blocks.size();
    std::set<std::vector<std::size_t>> certified_blocks;

    bool can_continue = true;
    if (has_non_singleton(blocks))
    {
        z3::solver initial_solver(context);
        for (const z3::expr &constraint : constraints)
            initial_solver.add(constraint);
        const auto check_started = clk::now();
        const z3::check_result check = initial_solver.check();
        output.statistics.check_time +=
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - check_started);
        ++output.statistics.checks;
        if (check == z3::sat)
        {
            ++output.statistics.sat_checks;
            refine_partition(
                blocks, terms, initial_solver.get_model(),
                output.statistics);
        }
        else if (check == z3::unsat)
        {
            ++output.statistics.unsat_checks;
            output.constraints_unsat = true;
            output.status = Status::Complete;
            can_continue = false;
        }
        else
        {
            output.status = Status::Unknown;
            output.diagnostic = initial_solver.reason_unknown();
            can_continue = false;
        }
    }

    std::vector<std::unique_ptr<ParallelWorkerState>> workers;
    if (can_continue && has_non_singleton(blocks))
    {
        workers.reserve(options.parallel_workers);
        for (std::size_t i = 0; i < options.parallel_workers; ++i)
            workers.push_back(std::make_unique<ParallelWorkerState>(
                context, constraints, terms));
    }

    while (can_continue)
    {
        std::vector<std::size_t> active_blocks;
        for (std::size_t i = 0; i < blocks.size(); ++i)
        {
            if (blocks[i].size() > 1 &&
                !certified_blocks.contains(blocks[i]))
                active_blocks.push_back(i);
        }
        if (active_blocks.empty())
            break;

        std::sort(
            active_blocks.begin(), active_blocks.end(),
            [&](std::size_t lhs, std::size_t rhs) {
                const std::size_t lhs_edges = blocks[lhs].size() - 1;
                const std::size_t rhs_edges = blocks[rhs].size() - 1;
                if (lhs_edges != rhs_edges)
                    return lhs_edges > rhs_edges;
                return blocks[lhs].front() < blocks[rhs].front();
            });

        std::vector<std::vector<std::size_t>> assignments(
            options.parallel_workers);
        std::vector<std::size_t> loads(options.parallel_workers, 0);
        for (std::size_t block_index : active_blocks)
        {
            const auto target = std::min_element(
                loads.begin(), loads.end());
            const std::size_t worker_index =
                static_cast<std::size_t>(target - loads.begin());
            assignments[worker_index].push_back(block_index);
            loads[worker_index] += blocks[block_index].size() - 1;
        }

        std::size_t active_queries = 0;
        for (const auto &assignment : assignments)
            if (!assignment.empty())
                ++active_queries;
        ++output.statistics.parallel_rounds;
        output.statistics.max_parallel_queries = std::max(
            output.statistics.max_parallel_queries, active_queries);

        std::vector<ParallelQueryResult> query_results(
            options.parallel_workers);
        std::vector<std::thread> threads;
        threads.reserve(active_queries);
        const unsigned round_seed = static_cast<unsigned>(
            output.statistics.parallel_rounds);
        for (std::size_t i = 0; i < assignments.size(); ++i)
        {
            if (assignments[i].empty())
                continue;
            threads.emplace_back([&, i] {
                query_results[i] = run_parallel_group_query(
                    *workers.at(i), blocks, assignments[i],
                    round_seed, 0);
            });
        }
        for (std::thread &thread : threads)
            thread.join();

        std::size_t round_sat = 0;
        std::size_t round_unsat = 0;
        bool round_failed = false;
        for (std::size_t i = 0; i < assignments.size(); ++i)
        {
            if (assignments[i].empty())
                continue;
            const ParallelQueryResult &query = query_results[i];
            ++output.statistics.checks;
            output.statistics.check_time += query.check_time;
            output.statistics.splitter_edges += query.splitter_edges;
            output.statistics.max_splitter_edges = std::max(
                output.statistics.max_splitter_edges,
                query.splitter_edges);
            if (query.outcome == ParallelQueryOutcome::Sat)
            {
                ++output.statistics.sat_checks;
                ++round_sat;
            }
            else if (query.outcome == ParallelQueryOutcome::Unsat)
            {
                ++output.statistics.unsat_checks;
                ++round_unsat;
                for (std::size_t block_index : assignments[i])
                    certified_blocks.insert(blocks.at(block_index));
            }
            else
            {
                round_failed = true;
                output.status =
                    query.outcome == ParallelQueryOutcome::Unknown
                        ? Status::Unknown
                        : Status::Error;
                output.diagnostic =
                    "parallel worker " + std::to_string(i) + ": " +
                    (query.diagnostic.empty()
                         ? std::string("query failed")
                         : query.diagnostic);
                break;
            }
        }
        if (round_failed)
        {
            can_continue = false;
            break;
        }

        std::size_t round_splits = 0;
        for (std::size_t i = 0; i < assignments.size(); ++i)
        {
            if (!assignments[i].empty() &&
                query_results[i].outcome ==
                    ParallelQueryOutcome::Sat)
                round_splits += refine_partition_with_values(
                    blocks, query_results[i].values,
                    output.statistics);
        }
        if (round_sat != 0 && round_splits == 0)
            throw std::runtime_error(
                "parallel BPR SAT round did not refine the partition");

        for (const auto &certified : certified_blocks)
        {
            if (std::find(
                    blocks.begin(), blocks.end(), certified) ==
                blocks.end())
                throw std::runtime_error(
                    "parallel BPR model split an UNSAT-certified block");
        }

        if (log)
            LOG_INFO(
                *log, "eqpartition",
                "parallel BPR round=" +
                    std::to_string(
                        output.statistics.parallel_rounds) +
                    " queries=" + std::to_string(active_queries) +
                    " sat=" + std::to_string(round_sat) +
                    " unsat=" + std::to_string(round_unsat) +
                    " blocks=" + std::to_string(blocks.size()) +
                    " certified=" +
                    std::to_string(certified_blocks.size()));
    }

    if (can_continue &&
        options.parallel_final_global_validation &&
        !output.constraints_unsat)
    {
        z3::solver validator(context);
        for (const z3::expr &constraint : constraints)
            validator.add(constraint);
        z3::expr_vector differences(context);
        for (const auto &block : blocks)
        {
            if (block.size() < 2)
                continue;
            const std::size_t representative = block.front();
            for (std::size_t i = 1; i < block.size(); ++i)
                differences.push_back(
                    terms.at(representative) !=
                    terms.at(block[i]));
        }
        output.statistics.splitter_edges += differences.size();
        output.statistics.max_splitter_edges = std::max(
            output.statistics.max_splitter_edges,
            static_cast<std::size_t>(differences.size()));
        if (differences.empty())
            validator.add(context.bool_val(false));
        else
            validator.add(z3::mk_or(differences));

        const auto check_started = clk::now();
        const z3::check_result check = validator.check();
        const auto validation_elapsed =
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - check_started);
        output.statistics.check_time += validation_elapsed;
        output.statistics.final_validation_time += validation_elapsed;
        ++output.statistics.checks;
        ++output.statistics.final_validation_checks;
        if (check == z3::unsat)
        {
            ++output.statistics.unsat_checks;
        }
        else if (check == z3::sat)
        {
            ++output.statistics.sat_checks;
            output.status = Status::Error;
            output.diagnostic =
                "final global validation returned SAT";
            can_continue = false;
        }
        else
        {
            output.status = Status::Unknown;
            output.diagnostic =
                "final global validation returned unknown: " +
                validator.reason_unknown();
            can_continue = false;
        }
        if (log)
            LOG_INFO(
                *log, "eqpartition",
                "parallel BPR final global validation: result=" +
                    std::string(
                        check == z3::unsat
                            ? "unsat"
                            : check == z3::sat ? "sat" : "unknown") +
                    " edges=" +
                    std::to_string(differences.size()) +
                    " elapsed=" +
                    util::fmt_duration(validation_elapsed));
    }

    if (can_continue && output.status == Status::Error)
        output.status = Status::Complete;
    const std::string parallel_diagnostic =
        "parallel-workers=" +
        std::to_string(options.parallel_workers) +
        " parallel-rounds=" +
        std::to_string(output.statistics.parallel_rounds) +
        " max-parallel-queries=" +
        std::to_string(output.statistics.max_parallel_queries) +
        " final-global-validation=" +
        (options.parallel_final_global_validation ? "true" : "false");
    if (output.diagnostic.empty())
        output.diagnostic = parallel_diagnostic;
    else
        output.diagnostic += " " + parallel_diagnostic;
    finalize_result(output, std::move(blocks));
    return output;
}

Result run_incremental_bpr(z3::context &context,
                           const std::vector<z3::expr> &constraints,
                           const std::vector<z3::expr> &terms,
                           Variant variant,
                           util::Logger *log)
{
    Result output;
    output.statistics.terms = terms.size();
    auto blocks = initial_partition(terms);
    output.statistics.initial_blocks = blocks.size();

    auto refine_with_model = [&](const z3::model &model) -> std::size_t {
        std::vector<std::vector<std::size_t>> refined;
        refined.reserve(blocks.size() + 1);
        std::size_t split_blocks = 0;
        for (const auto &block : blocks)
        {
            if (block.size() < 2)
            {
                if (!block.empty())
                    refined.emplace_back(1, block.front());
                continue;
            }
            std::map<std::string, std::vector<std::size_t>> by_value;
            for (std::size_t term_index : block)
                by_value[model.eval(terms[term_index], true).to_string()]
                    .push_back(term_index);
            if (by_value.size() > 1)
                ++split_blocks;
            for (auto &[value, part] : by_value)
                refined.push_back(std::move(part));
        }
        blocks = std::move(refined);
        if (split_blocks != 0)
        {
            ++output.statistics.refinements;
            output.statistics.blocks_split += split_blocks;
        }
        return split_blocks;
    };

    bool continue_refinement = std::any_of(
        blocks.begin(), blocks.end(),
        [](const auto &block) { return block.size() > 1; });

    z3::solver solver(context);
    for (const z3::expr &constraint : constraints)
        solver.add(constraint);

    if (continue_refinement)
    {
        const auto check_started = clk::now();
        const z3::check_result check = solver.check();
        output.statistics.check_time +=
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - check_started);
        ++output.statistics.checks;

        if (check == z3::sat)
        {
            ++output.statistics.sat_checks;
            refine_with_model(solver.get_model());
        }
        else if (check == z3::unsat)
        {
            ++output.statistics.unsat_checks;
            output.constraints_unsat = true;
            output.status = Status::Complete;
            continue_refinement = false;
        }
        else
        {
            output.status = Status::Unknown;
            output.diagnostic = solver.reason_unknown();
            continue_refinement = false;
        }
    }

    std::unordered_map<std::uint64_t, z3::expr> hipr_edges;
    std::size_t fresh_edges = 0;
    std::size_t reused_edges = 0;

    while (continue_refinement)
    {
        z3::expr_vector differences(context);
        for (const auto &block : blocks)
        {
            if (block.size() < 2)
                continue;
            const std::size_t representative = block.front();
            for (std::size_t i = 1; i < block.size(); ++i)
            {
                const std::size_t member = block[i];
                if (variant == Variant::Hipr)
                {
                    const std::uint64_t key = edge_key(representative, member);
                    auto found = hipr_edges.find(key);
                    if (found == hipr_edges.end())
                    {
                        auto inserted = hipr_edges.emplace(
                            key, terms[representative] != terms[member]);
                        found = inserted.first;
                        ++fresh_edges;
                    }
                    else
                    {
                        ++reused_edges;
                    }
                    differences.push_back(found->second);
                }
                else
                {
                    differences.push_back(
                        terms[representative] != terms[member]);
                    ++fresh_edges;
                }
            }
        }

        output.statistics.splitter_edges += differences.size();
        output.statistics.max_splitter_edges = std::max(
            output.statistics.max_splitter_edges,
            static_cast<std::size_t>(differences.size()));
        if (differences.empty())
        {
            output.status = Status::Complete;
            break;
        }

        const z3::expr splitter = z3::mk_or(differences);
        const bool scoped = variant == Variant::ScopedBpr;
        if (scoped)
            solver.push();
        solver.add(splitter);

        const auto check_started = clk::now();
        const z3::check_result check = solver.check();
        output.statistics.check_time +=
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - check_started);
        ++output.statistics.checks;

        if (log && output.statistics.checks % 25 == 0)
        {
            LOG_INFO(*log, "eqpartition",
                     std::string("partition variant progress: algorithm=") +
                         variant_name(variant) +
                         " checks=" +
                         std::to_string(output.statistics.checks) +
                         " blocks=" + std::to_string(blocks.size()) +
                         " splitter-edges=" +
                         std::to_string(differences.size()) +
                         " fresh-edges=" + std::to_string(fresh_edges) +
                         " reused-edges=" + std::to_string(reused_edges));
            log->flush();
        }

        if (check == z3::unsat)
        {
            ++output.statistics.unsat_checks;
            output.status = Status::Complete;
            continue_refinement = false;
        }
        else if (check == z3::unknown)
        {
            output.status = Status::Unknown;
            output.diagnostic = solver.reason_unknown();
            continue_refinement = false;
        }
        else
        {
            ++output.statistics.sat_checks;
            const std::size_t split_blocks =
                refine_with_model(solver.get_model());
            if (split_blocks == 0)
                throw std::runtime_error(
                    "SAT splitter model did not refine any partition block");
        }

        if (scoped)
            solver.pop();
    }

    if (output.status == Status::Error)
        output.status = Status::Complete;
    const std::string edge_diagnostic =
        "fresh-splitter-edges=" + std::to_string(fresh_edges) +
        " reused-splitter-edges=" + std::to_string(reused_edges);
    if (output.diagnostic.empty())
        output.diagnostic = edge_diagnostic;
    else
        output.diagnostic += " " + edge_diagnostic;
    finalize_result(output, std::move(blocks));
    return output;
}

Result run_ipr(z3::context &context,
               const std::vector<z3::expr> &constraints,
               const std::vector<z3::expr> &terms,
               bool assumption_based,
               util::Logger *log)
{
    const Variant variant =
        assumption_based ? Variant::Abipr : Variant::Ipr;
    Result output;
    output.statistics.terms = terms.size();
    auto blocks = initial_partition(terms);
    output.statistics.initial_blocks = blocks.size();

    if (!has_non_singleton(blocks))
    {
        output.status = Status::Complete;
        finalize_result(output, std::move(blocks));
        return output;
    }

    z3::solver solver(context);
    for (const z3::expr &constraint : constraints)
        solver.add(constraint);

    const auto initial_started = clk::now();
    const z3::check_result initial_check = solver.check();
    output.statistics.check_time +=
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            clk::now() - initial_started);
    ++output.statistics.checks;
    if (initial_check == z3::unsat)
    {
        ++output.statistics.unsat_checks;
        output.constraints_unsat = true;
        output.status = Status::Complete;
        finalize_result(output, std::move(blocks));
        return output;
    }
    if (initial_check == z3::unknown)
    {
        output.status = Status::Unknown;
        output.diagnostic = solver.reason_unknown();
        finalize_result(output, std::move(blocks));
        return output;
    }
    ++output.statistics.sat_checks;
    refine_partition(blocks, terms, solver.get_model(), output.statistics);
    if (!has_non_singleton(blocks))
    {
        output.status = Status::Complete;
        finalize_result(output, std::move(blocks));
        return output;
    }

    const std::size_t term_count = terms.size();
    const std::size_t leaf_base = term_count - 1;
    const std::size_t node_count = 2 * term_count - 1;
    std::size_t fresh_counter = 0;
    std::vector<z3::expr> propositions;
    propositions.reserve(node_count);
    for (std::size_t i = 0; i < node_count; ++i)
        propositions.push_back(
            fresh_bool(context, assumption_based ? "abipr-p" : "ipr-p",
                       fresh_counter));

    std::vector<z3::expr> activations;
    if (assumption_based)
    {
        activations.reserve(term_count);
        for (std::size_t i = 0; i < term_count; ++i)
            activations.push_back(
                fresh_bool(context, "abipr-a", fresh_counter));
    }

    std::size_t fresh_leaf_definitions = 0;
    std::size_t reused_heap_nodes = 0;
    std::size_t fresh_internal_definitions = 0;

    auto add_leaf_definition = [&](std::size_t term_index) {
        const std::vector<std::size_t> reps =
            representatives(blocks, term_count);
        const std::size_t leaf = leaf_base + term_index;
        const z3::expr definition =
            propositions[leaf] ==
            (terms[term_index] != terms[reps.at(term_index)]);
        if (assumption_based)
            solver.add(z3::implies(activations[term_index], definition));
        else
            solver.add(definition);
        ++fresh_leaf_definitions;
    };

    for (std::size_t term_index = 0; term_index < term_count; ++term_index)
        add_leaf_definition(term_index);
    for (std::size_t cursor = leaf_base; cursor > 0; --cursor)
    {
        const std::size_t node = cursor - 1;
        const std::size_t lhs = 2 * node + 1;
        const std::size_t rhs = lhs + 1;
        solver.add(propositions[node] ==
                   (propositions[lhs] || propositions[rhs]));
        ++fresh_internal_definitions;
    }
    solver.add(propositions.front());

    while (has_non_singleton(blocks))
    {
        const std::size_t current_edges = star_edge_count(blocks);
        output.statistics.splitter_edges += current_edges;
        output.statistics.max_splitter_edges = std::max(
            output.statistics.max_splitter_edges, current_edges);

        const auto check_started = clk::now();
        z3::check_result check = z3::unknown;
        if (assumption_based)
        {
            z3::expr_vector assumptions(context);
            for (const z3::expr &activation : activations)
                assumptions.push_back(activation);
            check = solver.check(assumptions);
        }
        else
        {
            check = solver.check();
        }
        output.statistics.check_time +=
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - check_started);
        ++output.statistics.checks;

        if (log && output.statistics.checks % 25 == 0)
        {
            LOG_INFO(*log, "eqpartition",
                     std::string("partition variant progress: algorithm=") +
                         variant_name(variant) +
                         " checks=" +
                         std::to_string(output.statistics.checks) +
                         " blocks=" + std::to_string(blocks.size()) +
                         " splitter-edges=" +
                         std::to_string(current_edges) +
                         " fresh-leaf-definitions=" +
                         std::to_string(fresh_leaf_definitions) +
                         " fresh-internal-definitions=" +
                         std::to_string(fresh_internal_definitions) +
                         " reused-heap-nodes=" +
                         std::to_string(reused_heap_nodes));
            log->flush();
        }

        if (check == z3::unsat)
        {
            ++output.statistics.unsat_checks;
            output.status = Status::Complete;
            break;
        }
        if (check == z3::unknown)
        {
            output.status = Status::Unknown;
            output.diagnostic = solver.reason_unknown();
            break;
        }

        ++output.statistics.sat_checks;
        const z3::model model = solver.get_model();
        std::vector<bool> node_is_true(node_count, false);
        for (std::size_t node = 0; node < node_count; ++node)
            node_is_true[node] =
                model.eval(propositions[node], true).is_true();

        const std::size_t split_blocks =
            refine_partition(blocks, terms, model, output.statistics);
        if (split_blocks == 0)
            throw std::runtime_error(
                "SAT IPR heap model did not refine any partition block");
        const std::vector<std::size_t> reps =
            representatives(blocks, term_count);

        std::function<void(std::size_t)> update_node =
            [&](std::size_t node) {
                if (!node_is_true[node])
                {
                    ++reused_heap_nodes;
                    return;
                }

                propositions[node] = fresh_bool(
                    context, assumption_based ? "abipr-p" : "ipr-p",
                    fresh_counter);
                if (node >= leaf_base)
                {
                    const std::size_t term_index = node - leaf_base;
                    const z3::expr definition =
                        propositions[node] ==
                        (terms[term_index] !=
                         terms[reps.at(term_index)]);
                    if (assumption_based)
                    {
                        activations[term_index] =
                            fresh_bool(context, "abipr-a", fresh_counter);
                        solver.add(z3::implies(
                            activations[term_index], definition));
                    }
                    else
                    {
                        solver.add(definition);
                    }
                    ++fresh_leaf_definitions;
                    return;
                }

                const std::size_t lhs = 2 * node + 1;
                const std::size_t rhs = lhs + 1;
                update_node(lhs);
                update_node(rhs);
                solver.add(propositions[node] ==
                           (propositions[lhs] || propositions[rhs]));
                ++fresh_internal_definitions;
            };
        update_node(0);
        solver.add(propositions.front());
    }

    if (output.status == Status::Error)
        output.status = Status::Complete;
    const std::string heap_diagnostic =
        "fresh-leaf-definitions=" +
        std::to_string(fresh_leaf_definitions) +
        " fresh-internal-definitions=" +
        std::to_string(fresh_internal_definitions) +
        " reused-heap-nodes=" + std::to_string(reused_heap_nodes);
    if (output.diagnostic.empty())
        output.diagnostic = heap_diagnostic;
    else
        output.diagnostic += " " + heap_diagnostic;
    finalize_result(output, std::move(blocks));
    return output;
}

Result run_space_optimized_pr(
    z3::context &context,
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms,
    bool term_sharing,
    util::Logger *log)
{
    const Variant variant = term_sharing ? Variant::Hsopr : Variant::Sopr;
    Result output;
    output.statistics.terms = terms.size();
    auto blocks = initial_partition(terms);
    output.statistics.initial_blocks = blocks.size();

    if (!has_non_singleton(blocks))
    {
        output.status = Status::Complete;
        finalize_result(output, std::move(blocks));
        return output;
    }

    z3::solver solver(context);
    for (const z3::expr &constraint : constraints)
        solver.add(constraint);

    const auto initial_started = clk::now();
    const z3::check_result initial_check = solver.check();
    output.statistics.check_time +=
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            clk::now() - initial_started);
    ++output.statistics.checks;
    if (initial_check == z3::unsat)
    {
        ++output.statistics.unsat_checks;
        output.constraints_unsat = true;
        output.status = Status::Complete;
        finalize_result(output, std::move(blocks));
        return output;
    }
    if (initial_check == z3::unknown)
    {
        output.status = Status::Unknown;
        output.diagnostic = solver.reason_unknown();
        finalize_result(output, std::move(blocks));
        return output;
    }
    ++output.statistics.sat_checks;
    refine_partition(blocks, terms, solver.get_model(), output.statistics);

    std::unordered_map<std::uint64_t, z3::expr> edge_cache;
    std::unordered_map<std::uint64_t, z3::expr> leaf_cache;
    std::unordered_map<std::uint64_t, z3::expr> internal_cache;
    std::size_t fresh_counter = 0;
    std::size_t fresh_edges = 0;
    std::size_t reused_edges = 0;
    std::size_t fresh_proposition_nodes = 0;
    std::size_t reused_proposition_nodes = 0;

    auto get_edge = [&](std::size_t lhs, std::size_t rhs) {
        const std::uint64_t key = edge_key(lhs, rhs);
        auto found = edge_cache.find(key);
        if (found != edge_cache.end())
        {
            ++reused_edges;
            return found->second;
        }
        auto inserted = edge_cache.emplace(key, terms[lhs] != terms[rhs]);
        ++fresh_edges;
        return inserted.first->second;
    };

    auto get_leaf_proposition = [&](std::size_t lhs, std::size_t rhs) {
        const std::uint64_t key = edge_key(lhs, rhs);
        auto found = leaf_cache.find(key);
        if (found != leaf_cache.end())
        {
            ++reused_edges;
            ++reused_proposition_nodes;
            return found->second;
        }
        const z3::expr edge = get_edge(lhs, rhs);
        const z3::expr proposition =
            fresh_bool(context, "sopr-leaf", fresh_counter);
        solver.add(proposition == edge);
        auto inserted = leaf_cache.emplace(key, proposition);
        ++fresh_proposition_nodes;
        return inserted.first->second;
    };

    std::function<z3::expr(const std::vector<z3::expr> &,
                           std::size_t, std::size_t)>
        join_propositions;
    join_propositions =
        [&](const std::vector<z3::expr> &nodes,
            std::size_t begin,
            std::size_t end) -> z3::expr {
            if (end - begin == 1)
                return nodes.at(begin);
            const std::size_t middle = begin + (end - begin) / 2;
            const z3::expr lhs =
                join_propositions(nodes, begin, middle);
            const z3::expr rhs =
                join_propositions(nodes, middle, end);
            const std::uint64_t key = edge_key(lhs.id(), rhs.id());
            auto found = internal_cache.find(key);
            if (found != internal_cache.end())
            {
                ++reused_proposition_nodes;
                return found->second;
            }
            const z3::expr proposition =
                fresh_bool(context, "sopr-node", fresh_counter);
            solver.add(proposition == (lhs || rhs));
            auto inserted = internal_cache.emplace(key, proposition);
            ++fresh_proposition_nodes;
            return inserted.first->second;
        };

    while (has_non_singleton(blocks))
    {
        z3::expr_vector hsopr_edges(context);
        std::vector<z3::expr> class_roots;
        std::size_t current_edges = 0;
        for (const auto &block : blocks)
        {
            if (block.size() < 2)
                continue;
            std::vector<z3::expr> class_leaves;
            if (!term_sharing)
                class_leaves.reserve(block.size() - 1);
            for (std::size_t i = 1; i < block.size(); ++i)
            {
                ++current_edges;
                if (term_sharing)
                    hsopr_edges.push_back(
                        get_edge(block[i - 1], block[i]));
                else
                    class_leaves.push_back(
                        get_leaf_proposition(block[i - 1], block[i]));
            }
            if (!term_sharing)
                class_roots.push_back(join_propositions(
                    class_leaves, 0, class_leaves.size()));
        }

        if (current_edges == 0)
        {
            output.status = Status::Complete;
            break;
        }
        output.statistics.splitter_edges += current_edges;
        output.statistics.max_splitter_edges = std::max(
            output.statistics.max_splitter_edges, current_edges);

        z3::expr splitter = term_sharing
                                ? z3::mk_or(hsopr_edges)
                                : join_propositions(
                                      class_roots, 0, class_roots.size());
        solver.add(splitter);

        const auto check_started = clk::now();
        const z3::check_result check = solver.check();
        output.statistics.check_time +=
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - check_started);
        ++output.statistics.checks;

        if (log && output.statistics.checks % 25 == 0)
        {
            LOG_INFO(*log, "eqpartition",
                     std::string("partition variant progress: algorithm=") +
                         variant_name(variant) +
                         " checks=" +
                         std::to_string(output.statistics.checks) +
                         " blocks=" + std::to_string(blocks.size()) +
                         " splitter-edges=" +
                         std::to_string(current_edges) +
                         " fresh-edges=" + std::to_string(fresh_edges) +
                         " reused-edges=" + std::to_string(reused_edges) +
                         " fresh-proposition-nodes=" +
                         std::to_string(fresh_proposition_nodes) +
                         " reused-proposition-nodes=" +
                         std::to_string(reused_proposition_nodes));
            log->flush();
        }

        if (check == z3::unsat)
        {
            ++output.statistics.unsat_checks;
            output.status = Status::Complete;
            break;
        }
        if (check == z3::unknown)
        {
            output.status = Status::Unknown;
            output.diagnostic = solver.reason_unknown();
            break;
        }

        ++output.statistics.sat_checks;
        const std::size_t split_blocks = refine_partition(
            blocks, terms, solver.get_model(), output.statistics);
        if (split_blocks == 0)
            throw std::runtime_error(
                "SAT space-optimized splitter model did not refine "
                "any partition block");
    }

    if (output.status == Status::Error)
        output.status = Status::Complete;
    const std::string space_diagnostic =
        "fresh-chain-edges=" + std::to_string(fresh_edges) +
        " reused-chain-edges=" + std::to_string(reused_edges) +
        " fresh-proposition-nodes=" +
        std::to_string(fresh_proposition_nodes) +
        " reused-proposition-nodes=" +
        std::to_string(reused_proposition_nodes);
    if (output.diagnostic.empty())
        output.diagnostic = space_diagnostic;
    else
        output.diagnostic += " " + space_diagnostic;
    finalize_result(output, std::move(blocks));
    return output;
}

} // namespace

const char *variant_name(Variant variant)
{
    switch (variant)
    {
    case Variant::Z3Mpm:
        return "z3-mpm";
    case Variant::ScopedBpr:
        return "scoped-bpr";
    case Variant::AccumulatingBpr:
        return "accumulating-bpr";
    case Variant::Hipr:
        return "hipr";
    case Variant::Ipr:
        return "ipr";
    case Variant::Abipr:
        return "abipr";
    case Variant::Sopr:
        return "sopr";
    case Variant::Hsopr:
        return "hsopr";
    case Variant::ParallelBpr:
        return "parallel-bpr";
    }
    return "unknown";
}

Result run_variant(z3::context &source_context,
                   const std::vector<z3::expr> &source_constraints,
                   const std::vector<z3::expr> &source_terms,
                   Variant variant,
                   util::Logger *log)
{
    return run_variant(
        source_context, source_constraints, source_terms, variant,
        VariantOptions{}, log);
}

Result run_variant(z3::context &source_context,
                   const std::vector<z3::expr> &source_constraints,
                   const std::vector<z3::expr> &source_terms,
                   Variant variant,
                   const VariantOptions &options,
                   util::Logger *log)
{
    Result output;
    const auto all_started = clk::now();
    try
    {
        z3::context context;
        std::vector<z3::expr> constraints;
        constraints.reserve(source_constraints.size());
        for (const z3::expr &constraint : source_constraints)
            constraints.emplace_back(
                context,
                Z3_translate(static_cast<Z3_context>(source_context),
                             static_cast<Z3_ast>(constraint),
                             static_cast<Z3_context>(context)));
        std::vector<z3::expr> terms;
        terms.reserve(source_terms.size());
        for (const z3::expr &term : source_terms)
            terms.emplace_back(
                context,
                Z3_translate(static_cast<Z3_context>(source_context),
                             static_cast<Z3_ast>(term),
                             static_cast<Z3_context>(context)));

        if (variant == Variant::Z3Mpm)
            output = run_z3_mpm(context, constraints, terms);
        else if (variant == Variant::Ipr)
            output = run_ipr(context, constraints, terms, false, log);
        else if (variant == Variant::Abipr)
            output = run_ipr(context, constraints, terms, true, log);
        else if (variant == Variant::Sopr)
            output = run_space_optimized_pr(
                context, constraints, terms, false, log);
        else if (variant == Variant::Hsopr)
            output = run_space_optimized_pr(
                context, constraints, terms, true, log);
        else if (variant == Variant::ParallelBpr)
            output = run_parallel_bpr(
                context, constraints, terms, options, log);
        else
            output = run_incremental_bpr(
                context, constraints, terms, variant, log);
    }
    catch (const z3::exception &ex)
    {
        output.status = Status::Error;
        output.diagnostic = ex.msg();
    }
    catch (const std::exception &ex)
    {
        output.status = Status::Error;
        output.diagnostic = ex.what();
    }
    output.statistics.elapsed =
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            clk::now() - all_started);

    if (log)
    {
        const auto &stats = output.statistics;
        LOG_INFO(*log, "eqpartition",
                 std::string("partition variant summary: algorithm=") +
                     variant_name(variant) +
                     " status=" + status_name(output.status) +
                     " terms=" + std::to_string(stats.terms) +
                     " blocks=" + std::to_string(stats.initial_blocks) +
                     "->" + std::to_string(stats.final_blocks) +
                     " checks=" + std::to_string(stats.checks) +
                     " sat=" + std::to_string(stats.sat_checks) +
                     " unsat=" + std::to_string(stats.unsat_checks) +
                     " parallel-rounds=" +
                     std::to_string(stats.parallel_rounds) +
                     " max-parallel-queries=" +
                     std::to_string(stats.max_parallel_queries) +
                     " final-validation-checks=" +
                     std::to_string(stats.final_validation_checks) +
                     " final-validation-time=" +
                     util::fmt_duration(stats.final_validation_time) +
                     " proof-edges=" +
                     std::to_string(stats.proof_edges) +
                     " implied-pairs=" +
                     std::to_string(stats.implied_pairs) +
                     " check-time=" +
                     util::fmt_duration(stats.check_time) +
                     " elapsed=" + util::fmt_duration(stats.elapsed) +
                     (output.diagnostic.empty()
                          ? std::string()
                          : " detail=" + output.diagnostic));
    }
    return output;
}

} // namespace util::eqpartition
