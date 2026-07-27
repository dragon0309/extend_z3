#include "util/implied_eq_partition_refiner.hpp"

#include <algorithm>
#include <condition_variable>
#include <map>
#include <mutex>
#include <numeric>
#include <stdexcept>
#include <thread>
#include <unordered_map>

#include "util/logger.hpp"

namespace util::eqpartition
{
namespace
{

using clk = std::chrono::steady_clock;

std::string sort_key(const z3::expr &term)
{
    // Terms of different SMT sorts cannot be compared for equality. The sort
    // string is stable inside the translated worker context and includes BV
    // widths, array domains/ranges, and uninterpreted sort names.
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
    {
        if (block.size() > 1)
            count += block.size() * (block.size() - 1) / 2;
    }
    return count;
}

} // namespace

struct ImpliedEqualityPartitionRefiner::Impl
{
    Options options;
    util::Logger *log = nullptr;
    std::unique_ptr<z3::context> context;
    std::vector<z3::expr> constraints;
    std::vector<z3::expr> terms;

    mutable std::mutex mutex;
    std::condition_variable done_cv;
    std::thread worker;
    Result result;
    bool started = false;
    bool done = false;

    Impl(z3::context &source_context,
         const std::vector<z3::expr> &source_constraints,
         const std::vector<z3::expr> &source_terms,
         const Options &requested_options,
         util::Logger *logger)
        : options(requested_options), log(logger),
          context(std::make_unique<z3::context>())
    {
        constraints.reserve(source_constraints.size());
        for (const z3::expr &constraint : source_constraints)
            constraints.emplace_back(
                *context,
                Z3_translate((Z3_context)source_context, (Z3_ast)constraint,
                             (Z3_context)*context));
        terms.reserve(source_terms.size());
        for (const z3::expr &term : source_terms)
            terms.emplace_back(
                *context,
                Z3_translate((Z3_context)source_context, (Z3_ast)term,
                             (Z3_context)*context));

        if (log)
            LOG_INFO(*log, "eqpartition",
                     "partition refiner initialized: terms=" +
                         std::to_string(terms.size()) +
                         " constraints=" +
                         std::to_string(constraints.size()) +
                         " timeout-ms=" +
                         std::to_string(options.timeout_ms) +
                         " completeness=" +
                         (options.timeout_ms == 0 ? "required" : "best-effort"));
    }

    ~Impl()
    {
        if (worker.joinable())
            worker.join();
    }

    void finish(Result output)
    {
        {
            std::lock_guard<std::mutex> lock(mutex);
            result = std::move(output);
            done = true;
        }
        done_cv.notify_all();
    }

    void run()
    {
        Result output;
        output.status = Status::Error;
        const auto all_started = clk::now();
        try
        {
            std::vector<std::vector<std::size_t>> blocks =
                initial_partition(terms);
            output.statistics.terms = terms.size();
            output.statistics.initial_blocks = blocks.size();

            auto refine_with_model =
                [&](const z3::model &model) -> std::size_t {
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

            // The first plain model is deliberately obtained without a large
            // disequality disjunction. It usually splits a coarse sort block
            // into almost-final value classes in one cheap check.
            if (continue_refinement)
            {
                z3::solver solver(*context);
                if (options.timeout_ms != 0)
                    solver.set("timeout", options.timeout_ms);
                for (const z3::expr &constraint : constraints)
                    solver.add(constraint);
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
                    if (log)
                        LOG_INFO(*log, "eqpartition",
                                 "initial model refinement: blocks=" +
                                     std::to_string(blocks.size()) +
                                     " check=" +
                                     std::to_string(output.statistics.checks));
                }
                else if (check == z3::unsat)
                {
                    // An inconsistent F entails every well-sorted equality.
                    ++output.statistics.unsat_checks;
                    output.constraints_unsat = true;
                    output.status = Status::Complete;
                    continue_refinement = false;
                }
                else
                {
                    output.diagnostic = solver.reason_unknown();
                    output.status = Status::Unknown;
                    continue_refinement = false;
                }
            }

            while (continue_refinement)
            {
                z3::expr_vector differences(*context);
                for (const auto &block : blocks)
                {
                    if (block.size() < 2)
                        continue;
                    const std::size_t representative = block.front();
                    for (std::size_t i = 1; i < block.size(); ++i)
                        differences.push_back(
                            terms[representative] != terms[block[i]]);
                }

                output.statistics.splitter_edges += differences.size();
                output.statistics.max_splitter_edges = std::max(
                    output.statistics.max_splitter_edges,
                    static_cast<std::size_t>(differences.size()));

                // With no remaining edge, every block is a singleton. Every
                // separation was witnessed by a concrete model, so the
                // partition is already complete without another solver call.
                if (differences.empty())
                {
                    output.status = Status::Complete;
                    break;
                }

                // A fresh solver per splitter avoids incremental phase/state
                // accumulation. Varying the deterministic seed improves model
                // diversity and is materially faster on cut0.
                z3::solver validator(*context);
                if (options.timeout_ms != 0)
                    validator.set("timeout", options.timeout_ms);
                validator.set(
                    "random_seed",
                    static_cast<unsigned>(output.statistics.checks));
                for (const z3::expr &constraint : constraints)
                    validator.add(constraint);
                validator.add(z3::mk_or(differences));
                const auto check_started = clk::now();
                const z3::check_result check = validator.check();
                const auto check_elapsed =
                    std::chrono::duration_cast<std::chrono::nanoseconds>(
                        clk::now() - check_started);
                ++output.statistics.checks;
                output.statistics.check_time += check_elapsed;
                if (log)
                    LOG_INFO(*log, "eqpartition",
                             "splitter check #" +
                                 std::to_string(output.statistics.checks) +
                                 " edges=" +
                                 std::to_string(differences.size()) +
                                 " blocks=" + std::to_string(blocks.size()) +
                                 " result=" +
                                 (check == z3::sat
                                      ? "sat"
                                      : (check == z3::unsat ? "unsat"
                                                            : "unknown")));

                if (check == z3::unsat)
                {
                    ++output.statistics.unsat_checks;
                    output.status = Status::Complete;
                    continue_refinement = false;
                    continue;
                }

                if (check == z3::unknown)
                {
                    output.diagnostic = validator.reason_unknown();
                    output.status = Status::Unknown;
                    continue_refinement = false;
                    continue;
                }

                ++output.statistics.sat_checks;
                const z3::model model = validator.get_model();
                const std::size_t split_blocks = refine_with_model(model);

                if (split_blocks == 0)
                    throw std::runtime_error(
                        "SAT splitter model did not refine any partition block");
            }

            if (output.status == Status::Error)
                output.status = Status::Complete;

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
            LOG_INFO(*log, "eqpartition",
                     "partition refiner finished: status=" +
                         std::string(status_name(output.status)) +
                         " constraints-unsat=" +
                         (output.constraints_unsat ? "true" : "false") +
                         " checks=" +
                         std::to_string(output.statistics.checks) +
                         " sat=" +
                         std::to_string(output.statistics.sat_checks) +
                         " unsat=" +
                         std::to_string(output.statistics.unsat_checks) +
                         " blocks=" +
                         std::to_string(output.statistics.initial_blocks) +
                         "->" +
                         std::to_string(output.statistics.final_blocks) +
                         " equality-classes=" +
                         std::to_string(output.statistics.equality_classes) +
                         " proof-edges=" +
                         std::to_string(output.statistics.proof_edges) +
                         " implied-pairs=" +
                         std::to_string(output.statistics.implied_pairs));
        finish(std::move(output));
    }

    void start()
    {
        std::lock_guard<std::mutex> lock(mutex);
        if (started)
            return;
        started = true;
        worker = std::thread([this] { run(); });
    }

    bool ready() const
    {
        std::lock_guard<std::mutex> lock(mutex);
        return done;
    }

    const Result &wait()
    {
        start();
        if (worker.joinable())
            worker.join();
        std::unique_lock<std::mutex> lock(mutex);
        done_cv.wait(lock, [this] { return done; });
        return result;
    }
};

ImpliedEqualityPartitionRefiner::ImpliedEqualityPartitionRefiner(
    z3::context &source_context,
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms,
    const Options &options,
    util::Logger *log)
    : m_impl(std::make_unique<Impl>(source_context, constraints, terms,
                                    options, log))
{
    if (options.start_async)
        m_impl->start();
}

ImpliedEqualityPartitionRefiner::~ImpliedEqualityPartitionRefiner() = default;

void ImpliedEqualityPartitionRefiner::start()
{
    m_impl->start();
}

bool ImpliedEqualityPartitionRefiner::ready() const
{
    return m_impl->ready();
}

const Result &ImpliedEqualityPartitionRefiner::wait()
{
    return m_impl->wait();
}

const char *status_name(Status status)
{
    switch (status)
    {
    case Status::Complete:
        return "complete";
    case Status::Unknown:
        return "unknown";
    case Status::Error:
        return "error";
    }
    return "error";
}

} // namespace util::eqpartition
