#include "util/implied_eq_partition_variants.hpp"

#include <algorithm>
#include <array>
#include <bitwuzla/cpp/bitwuzla.h>
#include <bitwuzla/cpp/parser.h>
#include <boolector/boolector.h>
#include <boost/multiprecision/cpp_int.hpp>
#include <cerrno>
#include <chrono>
#include <condition_variable>
#include <cstdio>
#include <cstdint>
#include <deque>
#include <functional>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <sys/types.h>
#include <sys/wait.h>
#include <thread>
#include <atomic>
#include <unordered_map>
#include <unistd.h>
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
    Canceled,
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

using ParallelEdge = std::pair<std::size_t, std::size_t>;

ParallelEdge ordered_edge(std::size_t lhs, std::size_t rhs)
{
    if (lhs > rhs)
        std::swap(lhs, rhs);
    return {lhs, rhs};
}

void collect_bv_constants(const z3::expr &expression,
                          std::map<std::string, z3::expr> &out)
{
    if (expression.is_const() && !expression.is_numeral() &&
        expression.get_sort().is_bv() &&
        expression.decl().decl_kind() == Z3_OP_UNINTERPRETED)
        out.emplace(expression.to_string(), expression);
    for (unsigned i = 0; i < expression.num_args(); ++i)
        collect_bv_constants(expression.arg(i), out);
}

void collect_defined_bv_constants(
    const z3::expr &expression,
    std::set<Z3_ast> &out)
{
    if (expression.is_and())
    {
        for (unsigned i = 0; i < expression.num_args(); ++i)
            collect_defined_bv_constants(expression.arg(i), out);
        return;
    }
    if (!expression.is_eq())
        return;
    const z3::expr lhs = expression.arg(0);
    if (lhs.is_const() && !lhs.is_numeral() && lhs.get_sort().is_bv() &&
        lhs.decl().decl_kind() == Z3_OP_UNINTERPRETED)
        out.insert(static_cast<Z3_ast>(lhs));
}

std::vector<z3::expr> free_bv_inputs(
    const std::vector<z3::expr> &constraints)
{
    std::map<std::string, z3::expr> constants;
    std::set<Z3_ast> defined;
    for (const z3::expr &constraint : constraints)
    {
        collect_bv_constants(constraint, constants);
        collect_defined_bv_constants(constraint, defined);
    }
    std::vector<z3::expr> inputs;
    for (const auto &[name, constant] : constants)
        if (!defined.contains(static_cast<Z3_ast>(constant)))
            inputs.push_back(constant);
    return inputs;
}

void collect_bitwuzla_qfbv_constants(
    const z3::expr &expression,
    std::map<std::string, z3::expr> &out)
{
    const z3::sort sort = expression.get_sort();
    if (!sort.is_bool() && !sort.is_bv())
        throw std::runtime_error(
            "Bitwuzla partition backend only supports QF_BV expressions; "
            "unsupported sort in " + expression.to_string());
    if (!expression.is_app())
        throw std::runtime_error(
            "Bitwuzla partition backend does not support quantified or "
            "bound-variable expressions");

    if (expression.decl().decl_kind() == Z3_OP_UNINTERPRETED)
    {
        if (!expression.is_const() || expression.is_numeral())
            throw std::runtime_error(
                "Bitwuzla partition backend does not yet support "
                "uninterpreted functions");
        out.emplace(expression.to_string(), expression);
    }
    for (unsigned i = 0; i < expression.num_args(); ++i)
        collect_bitwuzla_qfbv_constants(expression.arg(i), out);
}

Result run_bitwuzla_partition(
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms,
    unsigned timeout_ms,
    util::Logger *log)
{
    Result output;
    output.statistics.terms = terms.size();
    auto blocks = initial_partition(terms);
    output.statistics.initial_blocks = blocks.size();
    if (!has_non_singleton(blocks))
    {
        output.status = Status::Complete;
        output.diagnostic = "embedded-cpp-api=true";
        finalize_result(output, std::move(blocks));
        return output;
    }

    std::map<std::string, z3::expr> constants;
    for (const z3::expr &constraint : constraints)
        collect_bitwuzla_qfbv_constants(constraint, constants);
    for (const z3::expr &term : terms)
        collect_bitwuzla_qfbv_constants(term, constants);

    std::ostringstream smt;
    smt << "(set-logic QF_BV)\n";
    for (const auto &[name, constant] : constants)
        smt << "(declare-const " << name << ' '
            << constant.get_sort().to_string() << ")\n";
    for (const z3::expr &constraint : constraints)
        smt << "(assert " << constraint << ")\n";

    bitwuzla::TermManager term_manager;
    bitwuzla::Options bitwuzla_options;
    bitwuzla_options.set(bitwuzla::Option::PRODUCE_MODELS, 1);
    if (timeout_ms != 0)
        bitwuzla_options.set(
            bitwuzla::Option::TIME_LIMIT_PER, timeout_ms);
    std::ostringstream parser_output;
    std::ostringstream diagnostics;
    bitwuzla_options.set_diagnostic_output_stream(diagnostics);
    bitwuzla::parser::Parser parser(
        term_manager, bitwuzla_options, "smt2", &parser_output);
    parser.parse(smt.str(), true, false);
    const std::shared_ptr<bitwuzla::Bitwuzla> solver =
        parser.bitwuzla();

    std::vector<bitwuzla::Term> bitwuzla_terms;
    bitwuzla_terms.reserve(terms.size());
    for (const z3::expr &term : terms)
        bitwuzla_terms.push_back(parser.parse_term(term.to_string()));

    auto model_values = [&]() {
        std::vector<std::string> values;
        values.reserve(bitwuzla_terms.size());
        for (const bitwuzla::Term &term : bitwuzla_terms)
            values.push_back(solver->get_value(term).str(2));
        return values;
    };
    auto check = [&](const std::vector<bitwuzla::Term> &assumptions = {}) {
        const auto started = clk::now();
        const bitwuzla::Result result = solver->check_sat(assumptions);
        const auto elapsed =
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - started);
        output.statistics.check_time += elapsed;
        ++output.statistics.checks;
        if (result == bitwuzla::Result::SAT)
            ++output.statistics.sat_checks;
        else if (result == bitwuzla::Result::UNSAT)
            ++output.statistics.unsat_checks;
        if (log)
            LOG_INFO(
                *log, "eqpartition",
                "Bitwuzla C++ check=" +
                    std::to_string(output.statistics.checks) +
                    " result=" + std::to_string(result) +
                    " blocks=" + std::to_string(blocks.size()) +
                    " elapsed=" + util::fmt_duration(elapsed));
        return result;
    };

    bitwuzla::Result result = check();
    if (result == bitwuzla::Result::UNSAT)
    {
        output.constraints_unsat = true;
        output.status = Status::Complete;
        output.diagnostic = "embedded-cpp-api=true";
        finalize_result(output, std::move(blocks));
        return output;
    }
    if (result == bitwuzla::Result::UNKNOWN)
    {
        output.status = Status::Unknown;
        output.diagnostic =
            "Bitwuzla initial check returned unknown: " +
            diagnostics.str();
        finalize_result(output, std::move(blocks));
        return output;
    }
    refine_partition_with_values(
        blocks, model_values(), output.statistics);

    while (has_non_singleton(blocks))
    {
        std::vector<bitwuzla::Term> differences;
        for (const auto &block : blocks)
        {
            if (block.size() < 2)
                continue;
            const std::size_t representative = block.front();
            for (std::size_t i = 1; i < block.size(); ++i)
                differences.push_back(term_manager.mk_term(
                    bitwuzla::Kind::DISTINCT,
                    {bitwuzla_terms.at(representative),
                     bitwuzla_terms.at(block[i])}));
        }
        output.statistics.splitter_edges += differences.size();
        output.statistics.max_splitter_edges = std::max(
            output.statistics.max_splitter_edges,
            differences.size());
        if (differences.empty())
            break;

        const bitwuzla::Term splitter =
            differences.size() == 1
                ? differences.front()
                : term_manager.mk_term(bitwuzla::Kind::OR, differences);
        result = check({splitter});
        if (result == bitwuzla::Result::UNSAT)
        {
            output.status = Status::Complete;
            break;
        }
        if (result == bitwuzla::Result::UNKNOWN)
        {
            output.status = Status::Unknown;
            output.diagnostic =
                "Bitwuzla splitter check returned unknown: " +
                diagnostics.str();
            break;
        }

        const std::size_t split_blocks = refine_partition_with_values(
            blocks, model_values(), output.statistics);
        if (split_blocks == 0)
            throw std::runtime_error(
                "Bitwuzla SAT model did not refine any partition block");
    }

    if (output.status == Status::Error)
        output.status = Status::Complete;
    if (output.diagnostic.empty())
        output.diagnostic = "embedded-cpp-api=true";
    finalize_result(output, std::move(blocks));
    return output;
}

class NativePartitionWorker
{
public:
    virtual ~NativePartitionWorker() = default;
    virtual ParallelQueryResult check(
        const std::vector<ParallelEdge> &edges) = 0;
    virtual void cancel() {}
};

std::string qfbv_smt2_base(
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms)
{
    std::map<std::string, z3::expr> constants;
    for (const z3::expr &constraint : constraints)
        collect_bitwuzla_qfbv_constants(constraint, constants);
    for (const z3::expr &term : terms)
        collect_bitwuzla_qfbv_constants(term, constants);

    std::ostringstream smt;
    smt << "(set-logic QF_BV)\n";
    for (const auto &[name, constant] : constants)
        smt << "(declare-const " << name << ' '
            << constant.get_sort().to_string() << ")\n";
    for (const z3::expr &constraint : constraints)
        smt << "(assert " << constraint << ")\n";
    return smt.str();
}

bitwuzla::Options bitwuzla_worker_options(
    unsigned timeout_ms, std::size_t worker_index)
{
    bitwuzla::Options options;
    options.set(bitwuzla::Option::PRODUCE_MODELS, 1);
    options.set(
        bitwuzla::Option::SEED,
        static_cast<std::uint64_t>(worker_index + 1));
    if (timeout_ms != 0)
        options.set(bitwuzla::Option::TIME_LIMIT_PER, timeout_ms);
    return options;
}

class BitwuzlaPartitionWorker final : public NativePartitionWorker
{
    class CancelTerminator final : public bitwuzla::Terminator
    {
    public:
        std::atomic<bool> canceled{false};

        bool terminate() override
        {
            return canceled.load();
        }
    };

    bitwuzla::TermManager term_manager_;
    // Must outlive both parser_ and solver_, which retain this pointer.
    CancelTerminator terminator_;
    bitwuzla::Options options_;
    std::ostringstream parser_output_;
    std::ostringstream diagnostics_;
    bitwuzla::parser::Parser parser_;
    std::shared_ptr<bitwuzla::Bitwuzla> solver_;
    std::vector<bitwuzla::Term> terms_;

public:
    BitwuzlaPartitionWorker(
        const std::string &base_smt,
        const std::vector<z3::expr> &terms,
        unsigned timeout_ms,
        std::size_t worker_index)
        : options_(bitwuzla_worker_options(timeout_ms, worker_index)),
          parser_(term_manager_, options_, "smt2", &parser_output_)
    {
        options_.set_diagnostic_output_stream(diagnostics_);
        parser_.parse(base_smt, true, false);
        solver_ = parser_.bitwuzla();
        solver_->configure_terminator(&terminator_);
        terms_.reserve(terms.size());
        for (const z3::expr &term : terms)
            terms_.push_back(parser_.parse_term(term.to_string()));
    }

    ParallelQueryResult check(
        const std::vector<ParallelEdge> &edges) override
    {
        ParallelQueryResult output;
        output.splitter_edges = edges.size();
        try
        {
            std::vector<bitwuzla::Term> assumptions;
            if (!edges.empty())
            {
                std::vector<bitwuzla::Term> differences;
                differences.reserve(edges.size());
                for (const auto &[lhs, rhs] : edges)
                    differences.push_back(term_manager_.mk_term(
                        bitwuzla::Kind::DISTINCT,
                        {terms_.at(lhs), terms_.at(rhs)}));
                assumptions.push_back(
                    differences.size() == 1
                        ? differences.front()
                        : term_manager_.mk_term(
                              bitwuzla::Kind::OR, differences));
            }
            const auto started = clk::now();
            const bitwuzla::Result result =
                solver_->check_sat(assumptions);
            output.check_time =
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                    clk::now() - started);
            if (result == bitwuzla::Result::SAT)
            {
                output.outcome = ParallelQueryOutcome::Sat;
                output.values.reserve(terms_.size());
                for (const bitwuzla::Term &term : terms_)
                    output.values.push_back(
                        solver_->get_value(term).str(2));
            }
            else if (result == bitwuzla::Result::UNSAT)
                output.outcome = ParallelQueryOutcome::Unsat;
            else
            {
                output.outcome = terminator_.canceled.load()
                                     ? ParallelQueryOutcome::Canceled
                                     : ParallelQueryOutcome::Unknown;
                output.diagnostic = diagnostics_.str();
            }
        }
        catch (const std::exception &ex)
        {
            output.outcome = ParallelQueryOutcome::Error;
            output.diagnostic = ex.what();
        }
        return output;
    }

    void cancel() override
    {
        terminator_.canceled.store(true);
    }
};

class BoolectorPartitionWorker final : public NativePartitionWorker
{
    struct Deadline
    {
        std::atomic<bool> enabled{false};
        std::atomic<bool> canceled{false};
        clk::time_point at{};
    };

    Btor *btor_ = nullptr;
    z3::context &context_;
    unsigned timeout_ms_ = 0;
    bool one_shot_ = false;
    Deadline deadline_;
    std::unordered_map<Z3_ast, BoolectorNode *> nodes_;
    std::vector<BoolectorNode *> terms_;

    static int32_t terminate(void *state)
    {
        const auto *deadline = static_cast<const Deadline *>(state);
        return deadline->canceled.load() ||
               (deadline->enabled.load() &&
                clk::now() >= deadline->at);
    }

    BoolectorSort sort(const z3::sort &zsort)
    {
        if (zsort.is_bool())
            return boolector_bool_sort(btor_);
        if (zsort.is_bv())
            return boolector_bitvec_sort(btor_, zsort.bv_size());
        throw std::runtime_error(
            "Boolector partition backend only supports Bool and BV sorts");
    }

    BoolectorNode *fold(
        const std::vector<BoolectorNode *> &args,
        BoolectorNode *(*operation)(
            Btor *, BoolectorNode *, BoolectorNode *))
    {
        if (args.empty())
            throw std::runtime_error(
                "Boolector translator received an empty n-ary operator");
        BoolectorNode *result = args.front();
        bool owns_result = false;
        for (std::size_t i = 1; i < args.size(); ++i)
        {
            BoolectorNode *next = operation(btor_, result, args[i]);
            if (owns_result)
                boolector_release(btor_, result);
            result = next;
            owns_result = true;
        }
        return result;
    }

    BoolectorNode *translate(const z3::expr &expression)
    {
        const Z3_ast raw = static_cast<Z3_ast>(expression);
        const auto found = nodes_.find(raw);
        if (found != nodes_.end())
            return found->second;
        if (!expression.is_app())
            throw std::runtime_error(
                "Boolector partition backend does not support quantified "
                "or bound-variable expressions");

        BoolectorNode *result = nullptr;
        if (expression.is_true())
            result = boolector_true(btor_);
        else if (expression.is_false())
            result = boolector_false(btor_);
        else if (expression.is_numeral() &&
                 expression.get_sort().is_bv())
        {
            std::string bits = Z3_get_numeral_binary_string(
                static_cast<Z3_context>(context_), raw);
            const unsigned width = expression.get_sort().bv_size();
            if (bits.size() < width)
                bits.insert(0, width - bits.size(), '0');
            else if (bits.size() > width)
                bits.erase(0, bits.size() - width);
            result = boolector_const(btor_, bits.c_str());
        }
        else if (expression.decl().decl_kind() == Z3_OP_UNINTERPRETED)
        {
            if (!expression.is_const())
                throw std::runtime_error(
                    "Boolector partition backend does not support "
                    "uninterpreted functions");
            const BoolectorSort bsort = sort(expression.get_sort());
            const std::string symbol = expression.to_string();
            result = boolector_var(btor_, bsort, symbol.c_str());
            boolector_release_sort(btor_, bsort);
        }
        else
        {
            std::vector<BoolectorNode *> args;
            args.reserve(expression.num_args());
            for (unsigned i = 0; i < expression.num_args(); ++i)
                args.push_back(translate(expression.arg(i)));
            const Z3_decl_kind kind = expression.decl().decl_kind();
            switch (kind)
            {
            case Z3_OP_EQ:
            case Z3_OP_IFF:
                result = boolector_eq(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_DISTINCT:
            {
                std::vector<BoolectorNode *> pairs;
                for (std::size_t i = 0; i < args.size(); ++i)
                    for (std::size_t j = i + 1; j < args.size(); ++j)
                        pairs.push_back(boolector_ne(
                            btor_, args[i], args[j]));
                result = pairs.empty()
                             ? boolector_true(btor_)
                             : fold(pairs, boolector_and);
                break;
            }
            case Z3_OP_ITE:
                result = boolector_cond(
                    btor_, args.at(0), args.at(1), args.at(2));
                break;
            case Z3_OP_AND:
            case Z3_OP_BAND:
                result = fold(args, boolector_and);
                break;
            case Z3_OP_OR:
            case Z3_OP_BOR:
                result = fold(args, boolector_or);
                break;
            case Z3_OP_XOR:
            case Z3_OP_BXOR:
                result = fold(args, boolector_xor);
                break;
            case Z3_OP_BNAND:
                result = boolector_nand(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BNOR:
                result = boolector_nor(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BXNOR:
                result = boolector_xnor(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_NOT:
            case Z3_OP_BNOT:
                result = boolector_not(btor_, args.at(0));
                break;
            case Z3_OP_IMPLIES:
                result = boolector_implies(
                    btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BNEG:
                result = boolector_neg(btor_, args.at(0));
                break;
            case Z3_OP_BADD:
                result = fold(args, boolector_add);
                break;
            case Z3_OP_BSUB:
                result = boolector_sub(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BMUL:
                result = fold(args, boolector_mul);
                break;
            case Z3_OP_BUDIV:
            case Z3_OP_BUDIV_I:
                result = boolector_udiv(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BSDIV:
            case Z3_OP_BSDIV_I:
                result = boolector_sdiv(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BUREM:
            case Z3_OP_BUREM_I:
                result = boolector_urem(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BSREM:
            case Z3_OP_BSREM_I:
                result = boolector_srem(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BSMOD:
            case Z3_OP_BSMOD_I:
                result = boolector_smod(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_ULEQ:
                result = boolector_ulte(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_SLEQ:
                result = boolector_slte(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_UGEQ:
                result = boolector_ugte(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_SGEQ:
                result = boolector_sgte(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_ULT:
                result = boolector_ult(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_SLT:
                result = boolector_slt(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_UGT:
                result = boolector_ugt(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_SGT:
                result = boolector_sgt(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_CONCAT:
                result = fold(args, boolector_concat);
                break;
            case Z3_OP_SIGN_EXT:
                result = boolector_sext(
                    btor_, args.at(0),
                    Z3_get_decl_int_parameter(
                        static_cast<Z3_context>(context_),
                        static_cast<Z3_func_decl>(expression.decl()), 0));
                break;
            case Z3_OP_ZERO_EXT:
                result = boolector_uext(
                    btor_, args.at(0),
                    Z3_get_decl_int_parameter(
                        static_cast<Z3_context>(context_),
                        static_cast<Z3_func_decl>(expression.decl()), 0));
                break;
            case Z3_OP_EXTRACT:
                result = boolector_slice(
                    btor_, args.at(0),
                    Z3_get_decl_int_parameter(
                        static_cast<Z3_context>(context_),
                        static_cast<Z3_func_decl>(expression.decl()), 0),
                    Z3_get_decl_int_parameter(
                        static_cast<Z3_context>(context_),
                        static_cast<Z3_func_decl>(expression.decl()), 1));
                break;
            case Z3_OP_REPEAT:
                result = boolector_repeat(
                    btor_, args.at(0),
                    Z3_get_decl_int_parameter(
                        static_cast<Z3_context>(context_),
                        static_cast<Z3_func_decl>(expression.decl()), 0));
                break;
            case Z3_OP_BREDOR:
                result = boolector_redor(btor_, args.at(0));
                break;
            case Z3_OP_BREDAND:
                result = boolector_redand(btor_, args.at(0));
                break;
            case Z3_OP_BCOMP:
                result = boolector_eq(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BSHL:
                result = boolector_sll(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BLSHR:
                result = boolector_srl(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_BASHR:
                result = boolector_sra(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_ROTATE_LEFT:
                result = boolector_roli(
                    btor_, args.at(0),
                    Z3_get_decl_int_parameter(
                        static_cast<Z3_context>(context_),
                        static_cast<Z3_func_decl>(expression.decl()), 0));
                break;
            case Z3_OP_ROTATE_RIGHT:
                result = boolector_rori(
                    btor_, args.at(0),
                    Z3_get_decl_int_parameter(
                        static_cast<Z3_context>(context_),
                        static_cast<Z3_func_decl>(expression.decl()), 0));
                break;
            case Z3_OP_EXT_ROTATE_LEFT:
                result = boolector_rol(btor_, args.at(0), args.at(1));
                break;
            case Z3_OP_EXT_ROTATE_RIGHT:
                result = boolector_ror(btor_, args.at(0), args.at(1));
                break;
            default:
                throw std::runtime_error(
                    "unsupported Z3 operator in Boolector partition "
                    "backend: " + expression.decl().name().str());
            }
        }
        nodes_.emplace(raw, result);
        return result;
    }

public:
    BoolectorPartitionWorker(
        z3::context &context,
        const std::vector<z3::expr> &constraints,
        const std::vector<z3::expr> &terms,
        unsigned timeout_ms,
        std::size_t worker_index,
        bool one_shot = false,
        std::optional<unsigned> one_shot_seed = std::nullopt)
        : btor_(boolector_new()),
          context_(context),
          timeout_ms_(timeout_ms),
          one_shot_(one_shot)
    {
        if (!btor_)
            throw std::runtime_error("failed to create Boolector instance");
        try
        {
            boolector_set_opt(btor_, BTOR_OPT_AUTO_CLEANUP, 1);
            // Match the one-shot CLI's --model-gen mode. Incremental workers
            // need values for arbitrary partition terms across multiple
            // assumptions, so they retain the all-expression mode.
            boolector_set_opt(
                btor_, BTOR_OPT_MODEL_GEN, one_shot_ ? 1u : 2u);
            if (!one_shot_)
                boolector_set_opt(btor_, BTOR_OPT_INCREMENTAL, 1);
            boolector_set_opt(
                btor_, BTOR_OPT_SEED,
                one_shot_ ? one_shot_seed.value_or(0u)
                          : static_cast<uint32_t>(worker_index + 1));
            boolector_set_term(btor_, terminate, &deadline_);
            for (const z3::expr &constraint : constraints)
                boolector_assert(btor_, translate(constraint));
            terms_.reserve(terms.size());
            for (const z3::expr &term : terms)
                terms_.push_back(translate(term));
        }
        catch (...)
        {
            boolector_delete(btor_);
            btor_ = nullptr;
            throw;
        }
    }

    ~BoolectorPartitionWorker() override
    {
        if (btor_)
            boolector_delete(btor_);
    }

    ParallelQueryResult check(
        const std::vector<ParallelEdge> &edges) override
    {
        ParallelQueryResult output;
        output.splitter_edges = edges.size();
        try
        {
            BoolectorNode *splitter = nullptr;
            if (!edges.empty())
            {
                for (const auto &[lhs, rhs] : edges)
                {
                    BoolectorNode *difference = boolector_ne(
                        btor_, terms_.at(lhs), terms_.at(rhs));
                    if (!splitter)
                        splitter = difference;
                    else
                    {
                        BoolectorNode *combined = boolector_or(
                            btor_, splitter, difference);
                        boolector_release(btor_, splitter);
                        boolector_release(btor_, difference);
                        splitter = combined;
                    }
                }
                if (one_shot_)
                    boolector_assert(btor_, splitter);
                else
                    boolector_assume(btor_, splitter);
            }
            deadline_.enabled.store(timeout_ms_ != 0);
            if (deadline_.enabled.load())
                deadline_.at = clk::now() +
                               std::chrono::milliseconds(timeout_ms_);
            const auto started = clk::now();
            const int32_t result = boolector_sat(btor_);
            output.check_time =
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                    clk::now() - started);
            deadline_.enabled.store(false);
            if (splitter)
                boolector_release(btor_, splitter);
            if (result == BOOLECTOR_SAT)
            {
                output.outcome = ParallelQueryOutcome::Sat;
                output.values.reserve(terms_.size());
                for (BoolectorNode *term : terms_)
                {
                    const char *assignment =
                        boolector_bv_assignment(btor_, term);
                    output.values.emplace_back(assignment);
                    boolector_free_bv_assignment(btor_, assignment);
                }
            }
            else if (result == BOOLECTOR_UNSAT)
                output.outcome = ParallelQueryOutcome::Unsat;
            else
            {
                output.outcome = ParallelQueryOutcome::Unknown;
                output.diagnostic = "terminated or resource limited";
            }
        }
        catch (const std::exception &ex)
        {
            deadline_.enabled.store(false);
            output.outcome = ParallelQueryOutcome::Error;
            output.diagnostic = ex.what();
        }
        return output;
    }

    void cancel() override
    {
        deadline_.canceled.store(true);
    }
};

Result run_native_parallel_partition(
    z3::context &context,
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms,
    Variant variant,
    const VariantOptions &options,
    util::Logger *log)
{
    if (options.parallel_workers == 0)
        throw std::runtime_error(
            "native partition backend requires at least one worker");
    const std::string backend = variant_name(variant);
    const std::string base_smt =
        variant == Variant::Bitwuzla
            ? qfbv_smt2_base(constraints, terms)
            : std::string();

    std::vector<std::unique_ptr<NativePartitionWorker>> workers;
    workers.reserve(options.parallel_workers);
    for (std::size_t i = 0; i < options.parallel_workers; ++i)
    {
        if (variant == Variant::Bitwuzla)
            workers.push_back(std::make_unique<BitwuzlaPartitionWorker>(
                base_smt, terms, options.parallel_query_timeout_ms, i));
        else
            workers.push_back(std::make_unique<BoolectorPartitionWorker>(
                context, constraints, terms,
                options.parallel_query_timeout_ms, i));
    }

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

    ParallelQueryResult initial = workers.front()->check({});
    ++output.statistics.checks;
    output.statistics.check_time += initial.check_time;
    if (initial.outcome == ParallelQueryOutcome::Sat)
    {
        ++output.statistics.sat_checks;
        refine_partition_with_values(
            blocks, initial.values, output.statistics);
    }
    else if (initial.outcome == ParallelQueryOutcome::Unsat)
    {
        ++output.statistics.unsat_checks;
        output.constraints_unsat = true;
        output.status = Status::Complete;
        finalize_result(output, std::move(blocks));
        return output;
    }
    else
    {
        output.status = initial.outcome == ParallelQueryOutcome::Unknown
                            ? Status::Unknown
                            : Status::Error;
        output.diagnostic = "initial " + backend + " check: " +
                            initial.diagnostic;
        finalize_result(output, std::move(blocks));
        return output;
    }

    std::set<ParallelEdge> certified_edges;
    while (has_non_singleton(blocks))
    {
        std::vector<ParallelEdge> active_edges;
        for (const auto &block : blocks)
        {
            if (block.size() < 2)
                continue;
            const std::size_t representative = block.front();
            for (std::size_t i = 1; i < block.size(); ++i)
            {
                const ParallelEdge edge =
                    ordered_edge(representative, block[i]);
                if (!certified_edges.contains(edge))
                    active_edges.push_back(edge);
            }
        }
        if (active_edges.empty())
            break;

        std::vector<std::vector<ParallelEdge>> assignments(
            options.parallel_workers);
        for (std::size_t i = 0; i < active_edges.size(); ++i)
            assignments[i % options.parallel_workers].push_back(
                active_edges[i]);
        std::size_t active_queries = 0;
        for (const auto &assignment : assignments)
            active_queries += !assignment.empty();
        ++output.statistics.parallel_rounds;
        output.statistics.max_parallel_queries = std::max(
            output.statistics.max_parallel_queries, active_queries);

        std::vector<ParallelQueryResult> results(
            options.parallel_workers);
        std::vector<std::thread> threads;
        threads.reserve(active_queries);
        for (std::size_t i = 0; i < assignments.size(); ++i)
            if (!assignments[i].empty())
                threads.emplace_back([&, i] {
                    results[i] = workers[i]->check(assignments[i]);
                });
        for (std::thread &thread : threads)
            thread.join();

        std::size_t round_sat = 0;
        std::size_t round_unsat = 0;
        std::size_t round_unknown = 0;
        std::size_t round_splits = 0;
        for (std::size_t i = 0; i < assignments.size(); ++i)
        {
            if (assignments[i].empty())
                continue;
            const ParallelQueryResult &result = results[i];
            ++output.statistics.checks;
            output.statistics.check_time += result.check_time;
            output.statistics.splitter_edges += result.splitter_edges;
            output.statistics.max_splitter_edges = std::max(
                output.statistics.max_splitter_edges,
                result.splitter_edges);
            if (result.outcome == ParallelQueryOutcome::Sat)
            {
                ++output.statistics.sat_checks;
                ++round_sat;
                round_splits += refine_partition_with_values(
                    blocks, result.values, output.statistics);
            }
            else if (result.outcome == ParallelQueryOutcome::Unsat)
            {
                ++output.statistics.unsat_checks;
                ++round_unsat;
                certified_edges.insert(
                    assignments[i].begin(), assignments[i].end());
            }
            else if (result.outcome == ParallelQueryOutcome::Unknown)
            {
                ++output.statistics.parallel_unknown_checks;
                ++round_unknown;
            }
            else
            {
                output.status = Status::Error;
                output.diagnostic = backend + " worker " +
                                    std::to_string(i) + ": " +
                                    result.diagnostic;
                finalize_result(output, std::move(blocks));
                return output;
            }
        }
        if (log)
        {
            LOG_INFO(
                *log, "eqpartition",
                backend + " partition round=" +
                    std::to_string(output.statistics.parallel_rounds) +
                    " queries=" + std::to_string(active_queries) +
                    " sat=" + std::to_string(round_sat) +
                    " unsat=" + std::to_string(round_unsat) +
                    " unknown=" + std::to_string(round_unknown) +
                    " splits=" + std::to_string(round_splits) +
                    " blocks=" + std::to_string(blocks.size()) +
                    " active-edges=" +
                    std::to_string(active_edges.size()));
            log->flush();
        }
        if (round_sat == 0 && round_unsat == 0)
        {
            output.status = Status::Unknown;
            output.diagnostic = "all " + backend +
                                " worker queries returned unknown";
            break;
        }
        if (round_sat != 0 && round_splits == 0)
            throw std::runtime_error(
                backend + " SAT round did not refine the partition");
    }

    if (output.status == Status::Error)
        output.status = Status::Complete;
    const std::string api_detail =
        "embedded-api=true workers=" +
        std::to_string(options.parallel_workers);
    if (output.diagnostic.empty())
        output.diagnostic = api_detail;
    else
        output.diagnostic += "; " + api_detail;
    finalize_result(output, std::move(blocks));
    return output;
}

void apply_deterministic_seed_models(
    z3::context &context,
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms,
    std::vector<std::vector<std::size_t>> &blocks,
    Statistics &statistics,
    util::Logger *log)
{
    const std::vector<z3::expr> inputs = free_bv_inputs(constraints);
    // This is a small-input concrete-execution heuristic. Large independent
    // input vectors are unlikely to satisfy global range relations under a
    // fixed pattern and would only add redundant solver calls (for example,
    // cut0 exposes 256 free limbs).
    constexpr std::size_t MAX_SEED_INPUTS = 16;
    if (inputs.empty() || inputs.size() > MAX_SEED_INPUTS)
        return;

    // Structured concrete executions cheaply expose carry-dependent
    // disequalities that are difficult for an unconstrained QF_BV SAT search.
    // Values are assigned by stable input-name order and truncated naturally
    // by bv_val to each input width.
    std::vector<std::array<std::uint64_t, 4>> seeds{{
        {UINT64_C(0x0123456789abcdef),
         UINT64_C(0xfedcba9876543210),
         UINT64_C(0x1111111111111111),
         UINT64_C(0x2222222222222222)},
        {0, 0, 0, 0},
        {1, 1, 1, 1},
        {UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX},
        {UINT64_C(0xaaaaaaaaaaaaaaaa),
         UINT64_C(0x5555555555555555),
         UINT64_C(0xaaaaaaaaaaaaaaaa),
         UINT64_C(0x5555555555555555)},
        {1, 2, 4, 8},
        {UINT64_C(0x8000000000000000),
         UINT64_C(0x4000000000000000),
         UINT64_C(0x2000000000000000),
         UINT64_C(0x1000000000000000)},
        {UINT64_MAX, 0, UINT64_MAX, 0},
        {0, UINT64_MAX, 0, UINT64_MAX},
        {UINT64_C(0xffffffffffffffff),
         UINT64_C(0x00000000ffffffff),
         UINT64_C(0x0000000000000000),
         UINT64_C(0xffffffff00000001)},
        {UINT64_C(0xfffffffffffffffe),
         UINT64_C(0x00000000ffffffff),
         UINT64_C(0x0000000000000000),
         UINT64_C(0xffffffff00000001)},
        {UINT64_C(0xdeadbeefcafebabe),
         UINT64_C(0x9e3779b97f4a7c15),
         UINT64_C(0xd1b54a32d192ed03),
         UINT64_C(0x94d049bb133111eb)},
    }};
    // Add a deterministic pseudo-random concrete portfolio.  This is model
    // sampling only: every accepted seed is checked by Z3 against F and can
    // only split candidate blocks.  It never certifies an equality.
    auto splitmix64 = [](std::uint64_t &state) {
        state += UINT64_C(0x9e3779b97f4a7c15);
        std::uint64_t value = state;
        value = (value ^ (value >> 30)) *
                UINT64_C(0xbf58476d1ce4e5b9);
        value = (value ^ (value >> 27)) *
                UINT64_C(0x94d049bb133111eb);
        return value ^ (value >> 31);
    };
    std::uint64_t random_state = UINT64_C(0x6a09e667f3bcc909);
    constexpr std::size_t RANDOM_SEEDS = 52;
    for (std::size_t seed_index = 0;
         seed_index < RANDOM_SEEDS; ++seed_index)
    {
        std::array<std::uint64_t, 4> values{};
        for (std::uint64_t &value : values)
            value = splitmix64(random_state);
        seeds.push_back(values);
    }

    std::size_t consecutive_no_progress = 0;
    for (std::size_t seed_index = 0; seed_index < seeds.size(); ++seed_index)
    {
        z3::solver solver(context);
        for (const z3::expr &constraint : constraints)
            solver.add(constraint);
        for (std::size_t i = 0; i < inputs.size(); ++i)
        {
            std::uint64_t seed_value =
                seeds[seed_index][i % 4];
            if (i >= 4 && seed_index >= 12)
            {
                // Do not accidentally force distinct multi-limb operands to
                // the same repeating four-limb pattern.  Derive every extra
                // free input independently while preserving deterministic
                // replay across runs and worker counts.
                std::uint64_t input_state =
                    seed_value ^
                    (static_cast<std::uint64_t>(seed_index + 1) *
                     UINT64_C(0x9e3779b97f4a7c15)) ^
                    (static_cast<std::uint64_t>(i + 1) *
                     UINT64_C(0xd1b54a32d192ed03));
                seed_value = splitmix64(input_state);
            }
            const std::string numeral =
                std::to_string(seed_value);
            solver.add(
                inputs[i] == context.bv_val(
                    numeral.c_str(), inputs[i].get_sort().bv_size()));
        }
        const auto started = clk::now();
        const z3::check_result check = solver.check();
        const auto elapsed =
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - started);
        statistics.check_time += elapsed;
        ++statistics.checks;
        std::size_t split_blocks = 0;
        if (check == z3::sat)
        {
            ++statistics.sat_checks;
            split_blocks = refine_partition(
                blocks, terms, solver.get_model(), statistics);
        }
        else if (check == z3::unsat)
            ++statistics.unsat_checks;
        else
            ++statistics.parallel_unknown_checks;
        if (split_blocks == 0)
            ++consecutive_no_progress;
        else
            consecutive_no_progress = 0;
        if (log)
            LOG_INFO(
                *log, "eqpartition",
                "parallel BPR seed-model=" +
                    std::to_string(seed_index + 1) +
                    " inputs=" + std::to_string(inputs.size()) +
                    " result=" +
                    (check == z3::sat
                         ? std::string("sat")
                         : check == z3::unsat ? "unsat" : "unknown") +
                    " split-blocks=" +
                    std::to_string(split_blocks) +
                    " blocks=" + std::to_string(blocks.size()) +
                    " elapsed=" + util::fmt_duration(elapsed));
        if (seed_index >= 11 && consecutive_no_progress >= 8)
            break;
    }
}

std::optional<std::vector<std::string>> run_boolector_sat_witness(
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &inputs,
    const std::vector<ParallelEdge> &edges,
    const std::vector<z3::expr> &terms,
    unsigned timeout_seconds)
{
    if (inputs.empty() || edges.empty())
        return std::nullopt;

    std::map<std::string, z3::expr> constants;
    for (const z3::expr &constraint : constraints)
        collect_bv_constants(constraint, constants);
    std::ostringstream smt;
    smt << "(set-logic QF_BV)\n";
    for (const auto &[name, constant] : constants)
        smt << "(declare-const " << name << ' '
            << constant.get_sort().to_string() << ")\n";
    for (const z3::expr &constraint : constraints)
        smt << "(assert " << constraint << ")\n";
    smt << "(assert (or";
    for (const auto &[lhs, rhs] : edges)
        smt << " (distinct " << terms.at(lhs) << ' '
            << terms.at(rhs) << ')';
    smt << "))\n(check-sat)\n(get-value (";
    for (const z3::expr &input : inputs)
        smt << ' ' << input;
    smt << "))\n(exit)\n";
    const std::string request = smt.str();

    int input_pipe[2] = {-1, -1};
    int output_pipe[2] = {-1, -1};
    if (pipe(input_pipe) != 0 || pipe(output_pipe) != 0)
    {
        if (input_pipe[0] >= 0)
        {
            close(input_pipe[0]);
            close(input_pipe[1]);
        }
        return std::nullopt;
    }
    const pid_t pid = fork();
    if (pid == 0)
    {
        dup2(input_pipe[0], STDIN_FILENO);
        dup2(output_pipe[1], STDOUT_FILENO);
        dup2(output_pipe[1], STDERR_FILENO);
        close(input_pipe[0]);
        close(input_pipe[1]);
        close(output_pipe[0]);
        close(output_pipe[1]);
        const std::string timeout =
            std::to_string(std::max(1u, timeout_seconds));
        execl("/usr/bin/timeout", "timeout", "-s", "TERM", "-k", "5s",
              timeout.c_str(), "/usr/local/bin/boolector", "--smt2",
              "--model-gen", "--hex", "/dev/stdin",
              static_cast<char *>(nullptr));
        _exit(127);
    }
    close(input_pipe[0]);
    close(output_pipe[1]);
    if (pid < 0)
    {
        close(input_pipe[1]);
        close(output_pipe[0]);
        return std::nullopt;
    }
    std::size_t written = 0;
    while (written < request.size())
    {
        const ssize_t count = write(
            input_pipe[1], request.data() + written,
            request.size() - written);
        if (count < 0)
        {
            if (errno == EINTR)
                continue;
            break;
        }
        written += static_cast<std::size_t>(count);
    }
    close(input_pipe[1]);
    std::string response;
    std::array<char, 4096> buffer{};
    while (true)
    {
        const ssize_t count = read(
            output_pipe[0], buffer.data(), buffer.size());
        if (count < 0)
        {
            if (errno == EINTR)
                continue;
            break;
        }
        if (count == 0)
            break;
        response.append(buffer.data(), static_cast<std::size_t>(count));
    }
    close(output_pipe[0]);
    int status = 0;
    while (waitpid(pid, &status, 0) < 0 && errno == EINTR)
    {
    }
    if (!response.starts_with("sat"))
        return std::nullopt;

    std::vector<std::string> values;
    values.reserve(inputs.size());
    for (const z3::expr &input : inputs)
    {
        const std::string marker = "(" + input.to_string() + " ";
        const std::size_t position = response.find(marker);
        if (position == std::string::npos)
            return std::nullopt;
        const std::size_t begin = position + marker.size();
        const std::size_t end = response.find(')', begin);
        if (end == std::string::npos)
            return std::nullopt;
        values.push_back(response.substr(begin, end - begin));
    }
    return values;
}

struct BoolectorParserDeadline
{
    std::atomic<bool> enabled{false};
    const std::atomic<bool> *cancel_requested = nullptr;
    clk::time_point at{};
};

int32_t terminate_boolector_parser(void *state)
{
    const auto *deadline =
        static_cast<const BoolectorParserDeadline *>(state);
    return (deadline->cancel_requested &&
            deadline->cancel_requested->load()) ||
           (deadline->enabled.load() && clk::now() >= deadline->at);
}

ParallelQueryResult run_boolector_parser_global_witness(
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &inputs,
    const std::vector<ParallelEdge> &edges,
    const std::vector<z3::expr> &terms,
    unsigned timeout_ms,
    unsigned solver_seed = 0,
    const std::atomic<bool> *cancel_requested = nullptr)
{
    ParallelQueryResult output;
    output.splitter_edges = edges.size();
    if (inputs.empty() || edges.empty())
    {
        output.outcome = ParallelQueryOutcome::Error;
        output.diagnostic = "empty input or edge set";
        return output;
    }

    std::map<std::string, z3::expr> constants;
    for (const z3::expr &constraint : constraints)
        collect_bv_constants(constraint, constants);
    std::ostringstream smt;
    smt << "(set-logic QF_BV)\n";
    for (const auto &[name, constant] : constants)
        smt << "(declare-const " << name << ' '
            << constant.get_sort().to_string() << ")\n";
    for (const z3::expr &constraint : constraints)
        smt << "(assert " << constraint << ")\n";
    smt << "(assert (or";
    for (const auto &[lhs, rhs] : edges)
        smt << " (distinct " << terms.at(lhs) << ' '
            << terms.at(rhs) << ')';
    smt << "))\n(check-sat)\n";
    const std::string request = smt.str();

    FILE *input_file = std::tmpfile();
    FILE *output_file = std::tmpfile();
    if (!input_file || !output_file)
    {
        if (input_file)
            std::fclose(input_file);
        if (output_file)
            std::fclose(output_file);
        output.outcome = ParallelQueryOutcome::Error;
        output.diagnostic = "failed to create Boolector parser streams";
        return output;
    }
    if (std::fwrite(
            request.data(), 1, request.size(), input_file) !=
        request.size())
    {
        std::fclose(input_file);
        std::fclose(output_file);
        output.outcome = ParallelQueryOutcome::Error;
        output.diagnostic = "failed to write Boolector parser input";
        return output;
    }
    std::rewind(input_file);

    Btor *btor = boolector_new();
    if (!btor)
    {
        std::fclose(input_file);
        std::fclose(output_file);
        output.outcome = ParallelQueryOutcome::Error;
        output.diagnostic = "failed to create Boolector parser instance";
        return output;
    }
    boolector_set_opt(btor, BTOR_OPT_AUTO_CLEANUP, 1);
    boolector_set_opt(btor, BTOR_OPT_MODEL_GEN, 1);
    boolector_set_opt(btor, BTOR_OPT_SEED, solver_seed);
    BoolectorParserDeadline deadline;
    deadline.cancel_requested = cancel_requested;
    if (timeout_ms != 0)
    {
        deadline.at = clk::now() + std::chrono::milliseconds(timeout_ms);
        deadline.enabled.store(true);
    }
    boolector_set_term(btor, terminate_boolector_parser, &deadline);

    char *error_message = nullptr;
    int32_t expected_status = 0;
    const auto started = clk::now();
    const int32_t result = boolector_parse_smt2(
        btor, input_file, "embedded-global.smt2", output_file,
        &error_message, &expected_status);
    output.check_time =
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            clk::now() - started);
    deadline.enabled.store(false);

    if (result == BOOLECTOR_SAT)
    {
        output.outcome = ParallelQueryOutcome::Sat;
        output.values.reserve(inputs.size());
        for (const z3::expr &input : inputs)
        {
            const std::string symbol = input.to_string();
            BoolectorNode *node =
                boolector_match_node_by_symbol(btor, symbol.c_str());
            if (!node)
            {
                output.outcome = ParallelQueryOutcome::Error;
                output.diagnostic =
                    "Boolector model is missing input symbol: " + symbol;
                break;
            }
            const char *assignment =
                boolector_bv_assignment(btor, node);
            if (!assignment)
            {
                boolector_release(btor, node);
                output.outcome = ParallelQueryOutcome::Error;
                output.diagnostic =
                    "Boolector model has no BV assignment for: " + symbol;
                break;
            }
            output.values.emplace_back(assignment);
            boolector_free_bv_assignment(btor, assignment);
            boolector_release(btor, node);
        }
    }
    else if (result == BOOLECTOR_UNSAT)
        output.outcome = ParallelQueryOutcome::Unsat;
    else if (result == BOOLECTOR_UNKNOWN)
    {
        output.outcome = ParallelQueryOutcome::Unknown;
        output.diagnostic = "terminated or resource limited";
    }
    else
    {
        output.outcome = ParallelQueryOutcome::Error;
        output.diagnostic = error_message
                                ? std::string(error_message)
                                : "Boolector SMT2 parse failed";
    }

    boolector_delete(btor);
    std::fclose(input_file);
    std::fclose(output_file);
    return output;
}

std::optional<std::vector<std::string>> validate_global_input_witness(
    z3::context &context,
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms,
    const std::vector<ParallelEdge> &edges,
    const std::vector<z3::expr> &inputs,
    const std::vector<std::string> &input_values,
    unsigned timeout_ms)
{
    if (inputs.size() != input_values.size())
        return std::nullopt;
    z3::solver solver(context);
    solver.set("timeout", timeout_ms);
    for (const z3::expr &constraint : constraints)
        solver.add(constraint);
    for (std::size_t i = 0; i < inputs.size(); ++i)
    {
        std::string numeral = input_values[i];
        unsigned base = 10u;
        std::size_t digits_begin = 0;
        if (numeral.starts_with("#x") || numeral.starts_with("#b"))
        {
            base = numeral[1] == 'x' ? 16u : 2u;
            digits_begin = 2;
        }
        else if (inputs[i].get_sort().is_bv() &&
                 numeral.size() == inputs[i].get_sort().bv_size() &&
                 std::all_of(
                     numeral.begin(), numeral.end(),
                     [](char ch) { return ch == '0' || ch == '1'; }))
        {
            // Boolector's C API returns raw binary assignments without the
            // SMT-LIB #b prefix. Treat a full-width bit string as binary.
            base = 2u;
        }
        if (base != 10u)
        {
            boost::multiprecision::cpp_int value = 0;
            for (std::size_t j = digits_begin; j < numeral.size(); ++j)
            {
                const char ch = numeral[j];
                unsigned digit = ch >= '0' && ch <= '9'
                                     ? static_cast<unsigned>(ch - '0')
                                     : ch >= 'a' && ch <= 'f'
                                           ? static_cast<unsigned>(ch - 'a' + 10)
                                           : ch >= 'A' && ch <= 'F'
                                                 ? static_cast<unsigned>(ch - 'A' + 10)
                                                 : base;
                if (digit >= base)
                    return std::nullopt;
                value *= base;
                value += digit;
            }
            numeral = value.convert_to<std::string>();
        }
        Z3_ast raw_value = Z3_mk_numeral(
            static_cast<Z3_context>(context), numeral.c_str(),
            static_cast<Z3_sort>(inputs[i].get_sort()));
        solver.add(inputs[i] == z3::expr(context, raw_value));
    }
    z3::expr_vector differences(context);
    for (const auto &[lhs, rhs] : edges)
        differences.push_back(
            terms.at(lhs) != terms.at(rhs));
    // An empty edge set validates F + fixed inputs. This is sufficient for
    // partition refinement: any model of F may soundly split candidate
    // equality classes. The native global OR is only a witness-discovery
    // heuristic; it need not constrain Z3's completion. A non-empty edge set
    // remains available to callers that require exact-query validation.
    if (!differences.empty())
        solver.add(z3::mk_or(differences));
    if (solver.check() != z3::sat)
        return std::nullopt;
    const z3::model model = solver.get_model();
    std::vector<std::string> values;
    values.reserve(terms.size());
    for (const z3::expr &term : terms)
        values.push_back(model.eval(term, true).to_string());
    return values;
}

ParallelQueryResult run_parallel_group_query(
    ParallelWorkerState &worker,
    const std::vector<ParallelEdge> &edges,
    unsigned seed,
    unsigned timeout_ms,
    const std::atomic<bool> *cancel_requested = nullptr)
{
    ParallelQueryResult output;
    try
    {
        if (cancel_requested && cancel_requested->load())
        {
            output.outcome = ParallelQueryOutcome::Canceled;
            return output;
        }
        z3::solver solver(*worker.context);
        if (timeout_ms != 0)
            solver.set("timeout", timeout_ms);
        // Workers in the same round use the same deterministic seed. Query
        // diversity comes from disjoint edge groups, not a seed portfolio.
        solver.set("random_seed", seed);
        for (const z3::expr &constraint : worker.constraints)
            solver.add(constraint);

        z3::expr_vector differences(*worker.context);
        for (const auto &[lhs, rhs] : edges)
            differences.push_back(
                worker.terms.at(lhs) != worker.terms.at(rhs));
        output.splitter_edges = differences.size();
        if (differences.empty())
            throw std::runtime_error(
                "parallel BPR worker received an empty splitter");
        solver.add(z3::mk_or(differences));
        if (cancel_requested && cancel_requested->load())
        {
            output.outcome = ParallelQueryOutcome::Canceled;
            return output;
        }

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

std::optional<std::vector<std::string>>
validate_native_term_witness(
    z3::context &context,
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms,
    const std::vector<ParallelEdge> &edges,
    const std::vector<std::string> &native_values,
    std::chrono::nanoseconds &elapsed)
{
    if (native_values.size() != terms.size())
        return std::nullopt;
    const auto started = clk::now();
    z3::solver solver(context);
    for (const z3::expr &constraint : constraints)
        solver.add(constraint);
    for (std::size_t i = 0; i < terms.size(); ++i)
    {
        if (!terms[i].get_sort().is_bv())
            return std::nullopt;
        std::string bits = native_values[i];
        if (bits.rfind("#b", 0) == 0)
            bits.erase(0, 2);
        if (bits.empty() ||
            !std::all_of(bits.begin(), bits.end(),
                         [](char ch) {
                             return ch == '0' || ch == '1';
                         }))
            return std::nullopt;
        boost::multiprecision::cpp_int value = 0;
        for (const char bit : bits)
        {
            value <<= 1;
            value += bit == '1';
        }
        const std::string decimal = value.convert_to<std::string>();
        solver.add(
            terms[i] ==
            context.bv_val(
                decimal.c_str(), terms[i].get_sort().bv_size()));
    }
    z3::expr_vector differences(context);
    for (const auto &[lhs, rhs] : edges)
        differences.push_back(terms.at(lhs) != terms.at(rhs));
    if (!differences.empty())
        solver.add(z3::mk_or(differences));
    const z3::check_result check = solver.check();
    elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
        clk::now() - started);
    if (check != z3::sat)
        return std::nullopt;
    const z3::model model = solver.get_model();
    std::vector<std::string> values;
    values.reserve(terms.size());
    for (const z3::expr &term : terms)
        values.push_back(model.eval(term, true).to_string());
    return values;
}

Result run_global_edge_portfolio(
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
    std::set<ParallelEdge> certified_edges;
    bool can_continue = true;
    const std::vector<z3::expr> native_inputs =
        free_bv_inputs(constraints);
    std::optional<std::size_t> zero_anchor;
    const z3::expr bv1_zero = context.bv_val(0, 1);
    for (std::size_t i = 0; i < terms.size(); ++i)
        if (z3::eq(terms[i], bv1_zero))
        {
            zero_anchor = i;
            break;
    }
    if (zero_anchor)
        for (auto &block : blocks)
        {
            const auto position = std::find(
                block.begin(), block.end(), *zero_anchor);
            if (position != block.end())
            {
                std::rotate(block.begin(), position, position + 1);
                break;
            }
        }

    if (has_non_singleton(blocks))
    {
        z3::solver initial_solver(context);
        for (const z3::expr &constraint : constraints)
            initial_solver.add(constraint);
        const auto started = clk::now();
        const z3::check_result check = initial_solver.check();
        output.statistics.check_time +=
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - started);
        ++output.statistics.checks;
        if (check == z3::sat)
        {
            ++output.statistics.sat_checks;
            refine_partition(blocks, terms, initial_solver.get_model(),
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
            ++output.statistics.parallel_unknown_checks;
            output.status = Status::Unknown;
            output.diagnostic =
                "initial plain query returned unknown: " +
                initial_solver.reason_unknown();
            can_continue = false;
        }
    }

    if (can_continue && has_non_singleton(blocks))
        apply_deterministic_seed_models(
            context, constraints, terms, blocks,
            output.statistics, log);
    // Exact Boolector singleton checks run for every remaining BV1 zero-anchor
    // candidate in automatic mode. The general Z3 partition remains the
    // correctness path; these native SAT/UNSAT results only accelerate exact
    // singleton refinement/certification.
    if (can_continue && !options.z3_only && zero_anchor)
    {
        auto block_position = std::find_if(
            blocks.begin(), blocks.end(),
            [&](const std::vector<std::size_t> &block) {
                return std::find(
                           block.begin(), block.end(), *zero_anchor) !=
                       block.end();
            });
        if (block_position != blocks.end() && block_position->size() > 1)
        {
            std::vector<z3::expr> candidates;
            std::vector<std::size_t> candidate_indices;
            candidates.reserve(block_position->size() - 1);
            candidate_indices.reserve(block_position->size() - 1);
            for (const std::size_t index : *block_position)
                if (index != *zero_anchor)
                {
                    candidates.push_back(terms[index]);
                    candidate_indices.push_back(index);
                }

            const auto validation = run_native_bv1_singleton_queries(
                context, constraints, candidates,
                NativeSingletonBackend::Boolector,
                options.parallel_workers, 0, log);
            output.statistics.checks += validation.checks;
            output.statistics.sat_checks += validation.sat;
            output.statistics.unsat_checks += validation.unsat;
            output.statistics.parallel_unknown_checks +=
                validation.unknown;
            output.statistics.zero_singleton_checks +=
                validation.checks;
            output.statistics.zero_singleton_sat +=
                validation.sat;
            output.statistics.zero_singleton_unsat +=
                validation.unsat;
            output.statistics.zero_singleton_unknown +=
                validation.unknown;
            output.statistics.zero_singleton_time +=
                validation.elapsed;
            output.statistics.check_time += validation.elapsed;
            if (validation.unknown != 0)
            {
                output.status = Status::Unknown;
                output.diagnostic =
                    "zero-anchor accelerator returned unknown without a "
                    "production timeout";
                can_continue = false;
            }
            else
            {
                std::vector<std::size_t> zero_block{*zero_anchor};
                std::vector<std::size_t> nonzero_block;
                for (std::size_t i = 0; i < candidate_indices.size(); ++i)
                {
                    const std::size_t index = candidate_indices[i];
                    if (validation.outcomes.at(i) ==
                        NativeSingletonOutcome::Unsat)
                    {
                        zero_block.push_back(index);
                        certified_edges.insert(
                            ordered_edge(*zero_anchor, index));
                    }
                    else
                        nonzero_block.push_back(index);
                }
                *block_position = std::move(zero_block);
                if (!nonzero_block.empty())
                    blocks.insert(
                        std::next(block_position),
                        std::move(nonzero_block));
                if (log)
                {
                    LOG_INFO(
                        *log, "eqpartition",
                        "zero-anchor accelerator complete: candidates=" +
                            std::to_string(candidates.size()) +
                            " proved-zero=" +
                            std::to_string(validation.unsat) +
                            " refuted=" +
                            std::to_string(validation.sat) +
                            " elapsed=" +
                            util::fmt_duration(validation.elapsed));
                    log->flush();
                }
            }
        }
    }
    if (can_continue && options.z3_only && zero_anchor && log)
    {
        LOG_INFO(
            *log, "eqpartition",
            "zero-anchor accelerator disabled: z3-only=true");
        log->flush();
    }
    bool boolector_accelerator_supported = true;

    struct EpochTask
    {
        bool global = false;
        bool native_accelerator = false;
        bool native_input_witness = false;
        unsigned native_seed = 0;
        std::vector<ParallelEdge> edges;
        std::string label;
        std::unique_ptr<ParallelWorkerState> state;
        std::unique_ptr<NativePartitionWorker> native_worker;
        ParallelQueryResult result;
        std::thread thread;
        std::atomic<bool> cancel_requested{false};
        std::chrono::nanoseconds build_time{0};
        std::chrono::nanoseconds wall_time{0};
        std::chrono::nanoseconds validation_time{0};
        bool done = false;
        bool accounted = false;
        bool accepted = false;
        bool completed_before_cancel = false;
    };

    while (can_continue)
    {
        std::vector<ParallelEdge> active_edges;
        for (const auto &block : blocks)
        {
            if (block.size() < 2)
                continue;
            const std::size_t representative = block.front();
            for (std::size_t i = 1; i < block.size(); ++i)
            {
                const ParallelEdge edge =
                    ordered_edge(representative, block[i]);
                if (!certified_edges.contains(edge))
                    active_edges.push_back(edge);
            }
        }
        if (active_edges.empty())
            break;

        // Every feedback equality already has an UNSAT certificate relative
        // to the original constraints.  Adding those native BV facts to later
        // epochs is therefore equisatisfiable with the original query, while
        // exposing proved zero/equality information to backend preprocessing.
        // The facts are never present in the query that certifies themselves.
        std::vector<z3::expr> epoch_constraints = constraints;
        epoch_constraints.reserve(
            constraints.size() + certified_edges.size());
        for (const auto &[lhs, rhs] : certified_edges)
            epoch_constraints.push_back(
                terms.at(lhs) == terms.at(rhs));
        const std::size_t feedback_edge_count = certified_edges.size();

        std::vector<std::vector<ParallelEdge>> assignments(
            options.parallel_workers);
        assignments.front() = active_edges;
        std::map<unsigned, std::vector<ParallelEdge>> edges_by_width;
        for (const ParallelEdge &edge : active_edges)
            edges_by_width[terms.at(edge.first).get_sort().bv_size()]
                .push_back(edge);
        if (options.parallel_workers > 1)
        {
            // Keep one parser-based native global witness, then use every
            // remaining worker for independently certifiable edge chunks.
            // The first chunk is handled by Boolector-direct (when supported)
            // and the rest by Z3.  This avoids spending three of four workers
            // on the same global query, and is especially important when one
            // width is already almost fully certified.
            if (!options.z3_only)
                assignments[1] = active_edges;
            const std::size_t chunk_begin =
                options.z3_only ? 1 : 2;
            if (options.parallel_workers > chunk_begin)
            {
                const std::size_t edge_workers =
                    options.parallel_workers - chunk_begin;
                if (edges_by_width.size() == edge_workers)
                {
                    std::size_t worker = chunk_begin;
                    for (const auto &[width, edges] : edges_by_width)
                    {
                        (void) width;
                        assignments[worker++] = edges;
                    }
                }
                else
                    for (std::size_t i = 0; i < active_edges.size(); ++i)
                        assignments[
                            chunk_begin + i % edge_workers]
                            .push_back(active_edges[i]);
            }
        }

        std::vector<std::unique_ptr<EpochTask>> tasks;
        tasks.reserve(options.parallel_workers);
        for (std::size_t i = 0; i < assignments.size(); ++i)
        {
            if (assignments[i].empty())
                continue;
            const auto build_started = clk::now();
            auto task = std::make_unique<EpochTask>();
            task->global = i == 0;
            task->edges = std::move(assignments[i]);
            task->label = i == 0 ? "z3-global" : "z3-edge";
            if (!options.z3_only && (i == 1 || i == 2) &&
                boolector_accelerator_supported)
            {
                try
                {
                    task->native_seed =
                        static_cast<unsigned>(
                            output.statistics.parallel_rounds * 2 +
                            (i - 1));
                    // Constructing the direct worker is also the centralized
                    // lossless-QF_BV capability check.
                    task->native_worker =
                        std::make_unique<BoolectorPartitionWorker>(
                            context, epoch_constraints, terms, 0, i, true,
                            task->native_seed);
                    task->label = "boolector-direct";
                    task->native_accelerator = true;
                    task->global =
                        task->edges.size() == active_edges.size();
                    if (!native_inputs.empty() && i == 1)
                    {
                        // The parser-based one-shot mode has materially better
                        // preprocessing and witness search than the C-AST path
                        // on wide multiplication.  It returns only free inputs;
                        // Z3 completes and validates the full model before use.
                        task->native_input_witness = true;
                        task->label = "boolector-parser";
                        task->native_worker.reset();
                    }
                }
                catch (const std::exception &ex)
                {
                    boolector_accelerator_supported = false;
                    if (log)
                        LOG_INFO(
                            *log, "eqpartition",
                            "automatic Boolector accelerator disabled: " +
                                std::string(ex.what()));
                }
            }
            if (!task->native_accelerator)
                task->state =
                    std::make_unique<ParallelWorkerState>(
                        context, epoch_constraints, terms);
            task->build_time =
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                    clk::now() - build_started);
            tasks.push_back(std::move(task));
        }

        ++output.statistics.parallel_rounds;
        output.statistics.max_parallel_queries = std::max(
            output.statistics.max_parallel_queries, tasks.size());
        output.statistics.max_splitter_edges = std::max(
            output.statistics.max_splitter_edges, active_edges.size());

        if (log)
        {
            std::ostringstream width_loads;
            bool first_width = true;
            for (const auto &[width, edges] : edges_by_width)
            {
                if (!first_width)
                    width_loads << ',';
                first_width = false;
                width_loads << width << ':' << edges.size();
            }
            LOG_INFO(
                *log, "eqpartition",
                "global-edge BPR epoch-start=" +
                    std::to_string(output.statistics.parallel_rounds) +
                    " active-edges=" +
                    std::to_string(active_edges.size()) +
                    " queries=" + std::to_string(tasks.size()) +
                    " native-portfolio=" +
                    (options.z3_only ? "disabled" : "automatic") +
                    " width-loads=[" + width_loads.str() + "]");
            log->flush();
        }

        std::mutex completion_mutex;
        std::condition_variable completion_cv;
        std::deque<std::size_t> completed;
        const unsigned epoch_seed = static_cast<unsigned>(
            output.statistics.parallel_rounds);
        for (std::size_t i = 0; i < tasks.size(); ++i)
        {
            EpochTask *task = tasks[i].get();
            task->thread = std::thread([&, i, task] {
                const auto task_started = clk::now();
                if (task->native_input_witness)
                    task->result =
                        run_boolector_parser_global_witness(
                            epoch_constraints, native_inputs, task->edges,
                            terms, 0, task->native_seed,
                            &task->cancel_requested);
                else if (task->native_accelerator)
                    task->result =
                        task->native_worker->check(task->edges);
                else
                    task->result = run_parallel_group_query(
                        *task->state, task->edges,
                        epoch_seed * static_cast<unsigned>(
                                         options.parallel_workers) +
                            static_cast<unsigned>(i) + 1,
                        options.parallel_query_timeout_ms,
                        &task->cancel_requested);
                if (task->cancel_requested.load() &&
                    task->result.outcome ==
                        ParallelQueryOutcome::Unknown)
                    task->result.outcome =
                        ParallelQueryOutcome::Canceled;
                task->wall_time =
                    std::chrono::duration_cast<std::chrono::nanoseconds>(
                        clk::now() - task_started);
                {
                    std::lock_guard<std::mutex> lock(completion_mutex);
                    task->done = true;
                    completed.push_back(i);
                }
                completion_cv.notify_one();
            });
        }

        auto record_result = [&](EpochTask &task, bool accepted) {
            if (task.accounted)
                return;
            task.accounted = true;
            task.accepted = accepted;
            ++output.statistics.checks;
            output.statistics.check_time += task.result.check_time;
            output.statistics.splitter_edges +=
                task.result.splitter_edges;
            output.statistics.max_splitter_edges = std::max(
                output.statistics.max_splitter_edges,
                task.result.splitter_edges);
            if (task.native_accelerator)
            {
                ++output.statistics.parallel_fallback_checks;
                output.statistics.parallel_fallback_time +=
                    task.result.check_time;
            }
            if (!accepted)
            {
                if (task.cancel_requested.load() ||
                    task.result.outcome ==
                        ParallelQueryOutcome::Canceled)
                    ++output.statistics.parallel_canceled_checks;
                else
                    ++output.statistics.parallel_stale_checks;
                return;
            }
            if (task.result.outcome ==
                ParallelQueryOutcome::Canceled)
            {
                ++output.statistics.parallel_canceled_checks;
                return;
            }
            if (task.result.outcome == ParallelQueryOutcome::Sat)
            {
                ++output.statistics.sat_checks;
                if (task.native_accelerator)
                    ++output.statistics.parallel_fallback_sat;
            }
            else if (task.result.outcome ==
                     ParallelQueryOutcome::Unsat)
            {
                ++output.statistics.unsat_checks;
                if (task.native_accelerator)
                    ++output.statistics.parallel_fallback_unsat;
            }
            else if (task.result.outcome ==
                     ParallelQueryOutcome::Unknown)
            {
                ++output.statistics.parallel_unknown_checks;
                if (task.native_accelerator)
                    ++output.statistics.parallel_fallback_unknown;
            }
        };

        auto all_edges_certified = [&]() {
            return std::all_of(
                active_edges.begin(), active_edges.end(),
                [&](const ParallelEdge &edge) {
                    return certified_edges.contains(edge);
                });
        };

        bool decisive = false;
        bool have_sat_model = false;
        bool global_unknown = false;
        std::string winning_task = "none";
        std::vector<std::vector<std::string>> sat_models;
        std::size_t remaining = tasks.size();
        while (remaining != 0 && !decisive)
        {
            std::size_t index = 0;
            {
                std::unique_lock<std::mutex> lock(completion_mutex);
                completion_cv.wait(
                    lock, [&] { return !completed.empty(); });
                index = completed.front();
                completed.pop_front();
            }
            --remaining;
            EpochTask &task = *tasks[index];
            if (task.native_accelerator &&
                task.result.outcome == ParallelQueryOutcome::Sat)
            {
                std::chrono::nanoseconds validation_time{0};
                std::optional<std::vector<std::string>> validated;
                if (task.native_input_witness)
                {
                    const auto validation_started = clk::now();
                    validated = validate_global_input_witness(
                        context, epoch_constraints, terms, {}, native_inputs,
                        task.result.values, 0);
                    validation_time =
                        std::chrono::duration_cast<std::chrono::nanoseconds>(
                            clk::now() - validation_started);
                }
                else
                    validated = validate_native_term_witness(
                        context, epoch_constraints, terms, task.edges,
                        task.result.values, validation_time);
                task.validation_time += validation_time;
                ++output.statistics.checks;
                output.statistics.check_time += validation_time;
                if (validated)
                {
                    ++output.statistics.sat_checks;
                    task.result.values = *validated;
                }
                else
                {
                    ++output.statistics.parallel_unknown_checks;
                    task.result.outcome =
                        ParallelQueryOutcome::Unknown;
                    task.result.diagnostic =
                        "native SAT witness failed Z3 validation";
                }
            }
            record_result(task, true);
            const ParallelQueryOutcome outcome =
                task.result.outcome;
            if (outcome == ParallelQueryOutcome::Sat)
            {
                have_sat_model = true;
                sat_models.push_back(task.result.values);
                if (task.global)
                    ++output.statistics.global_sat_wins;
                else
                    ++output.statistics.chunk_sat_wins;
                winning_task = task.label;
                decisive = true;
            }
            else if (outcome == ParallelQueryOutcome::Unsat)
            {
                if (task.global)
                {
                    certified_edges.insert(
                        active_edges.begin(), active_edges.end());
                    ++output.statistics.global_unsat_wins;
                    winning_task = task.label;
                    decisive = true;
                }
                else
                {
                    certified_edges.insert(
                        task.edges.begin(), task.edges.end());
                    if (all_edges_certified())
                    {
                        ++output.statistics
                              .chunk_certificate_completions;
                        winning_task = "edge-certificates";
                        decisive = true;
                    }
                }
            }
            else if (outcome == ParallelQueryOutcome::Unknown)
            {
                if (task.global && !task.native_accelerator)
                    global_unknown = true;
            }
            else if (outcome == ParallelQueryOutcome::Error)
            {
                if (task.global && !task.native_accelerator)
                {
                    output.status = Status::Error;
                    output.diagnostic =
                        "global Z3 leader failed: " +
                        task.result.diagnostic;
                    can_continue = false;
                    decisive = true;
                }
                else
                {
                    if (task.native_accelerator)
                        boolector_accelerator_supported = false;
                    if (log)
                        LOG_INFO(
                            *log, "eqpartition",
                            "edge accelerator failed; global leader continues: " +
                                task.result.diagnostic);
                }
            }
        }

        if (decisive)
        {
            {
                std::lock_guard<std::mutex> lock(completion_mutex);
                for (auto &task : tasks)
                    if (!task->done)
                        task->cancel_requested.store(true);
                    else if (!task->accounted)
                        task->completed_before_cancel = true;
            }
            for (;;)
            {
                std::vector<EpochTask *> pending;
                {
                    std::lock_guard<std::mutex> lock(
                        completion_mutex);
                    for (auto &task : tasks)
                        if (!task->done)
                            pending.push_back(task.get());
                }
                if (pending.empty())
                    break;
                // Repeat interrupts until every canceled query publishes
                // completion. This closes the check-start TOCTOU window:
                // an interrupt issued before solver.check() is followed by
                // another after that procedure starts.
                for (EpochTask *task : pending)
                {
                    if (task->native_accelerator)
                    {
                        if (task->native_worker)
                            task->native_worker->cancel();
                    }
                    else
                        Z3_interrupt(static_cast<Z3_context>(
                            *task->state->context));
                }
                std::unique_lock<std::mutex> lock(completion_mutex);
                completion_cv.wait_for(
                    lock, std::chrono::milliseconds(2));
            }
        }
        for (auto &task : tasks)
            if (task->thread.joinable())
                task->thread.join();
        // Harvest every result that had already completed when the decisive
        // result was observed.  This adds no grace period and cannot delay
        // cancellation, but preserves useful SAT models and edge certificates
        // that otherwise depended on completion-queue ordering.
        for (auto &task : tasks)
        {
            if (task->accounted)
                continue;
            const bool accepted =
                !decisive || task->completed_before_cancel;
            if (accepted && task->native_accelerator &&
                task->result.outcome == ParallelQueryOutcome::Sat)
            {
                std::chrono::nanoseconds validation_time{0};
                std::optional<std::vector<std::string>> validated;
                if (task->native_input_witness)
                {
                    const auto validation_started = clk::now();
                    validated = validate_global_input_witness(
                        context, epoch_constraints, terms, {}, native_inputs,
                        task->result.values, 0);
                    validation_time =
                        std::chrono::duration_cast<std::chrono::nanoseconds>(
                            clk::now() - validation_started);
                }
                else
                    validated = validate_native_term_witness(
                        context, epoch_constraints, terms, task->edges,
                        task->result.values, validation_time);
                task->validation_time += validation_time;
                ++output.statistics.checks;
                output.statistics.check_time += validation_time;
                if (validated)
                {
                    ++output.statistics.sat_checks;
                    task->result.values = *validated;
                }
                else
                {
                    ++output.statistics.parallel_unknown_checks;
                    task->result.outcome = ParallelQueryOutcome::Unknown;
                    task->result.diagnostic =
                        "native SAT witness failed Z3 validation";
                }
            }
            record_result(*task, accepted);
            if (!accepted)
                continue;
            if (task->result.outcome == ParallelQueryOutcome::Sat)
            {
                have_sat_model = true;
                sat_models.push_back(task->result.values);
            }
            else if (task->result.outcome ==
                     ParallelQueryOutcome::Unsat)
                certified_edges.insert(
                    task->edges.begin(), task->edges.end());
        }

        if (log)
        {
            auto outcome_name = [](ParallelQueryOutcome outcome) {
                switch (outcome)
                {
                case ParallelQueryOutcome::Sat:
                    return "sat";
                case ParallelQueryOutcome::Unsat:
                    return "unsat";
                case ParallelQueryOutcome::Unknown:
                    return "unknown";
                case ParallelQueryOutcome::Canceled:
                    return "canceled";
                case ParallelQueryOutcome::Error:
                    return "error";
                }
                return "invalid";
            };
            for (std::size_t i = 0; i < tasks.size(); ++i)
            {
                const EpochTask &task = *tasks[i];
                LOG_INFO(
                    *log, "eqpartition",
                    "global-edge task epoch=" +
                        std::to_string(
                            output.statistics.parallel_rounds) +
                        " index=" + std::to_string(i) +
                        " label=" + task.label +
                        " edges=" +
                        std::to_string(task.edges.size()) +
                        " outcome=" +
                        outcome_name(task.result.outcome) +
                        " accepted=" +
                        (task.accepted ? "true" : "false") +
                        " feedback-edges=" +
                        std::to_string(feedback_edge_count) +
                        " build=" +
                        util::fmt_duration(task.build_time) +
                        " check=" +
                        util::fmt_duration(task.result.check_time) +
                        " validation=" +
                        util::fmt_duration(task.validation_time) +
                        " wall=" +
                        util::fmt_duration(task.wall_time));
            }
            log->flush();
        }

        if (!can_continue)
            break;
        if (have_sat_model)
        {
            std::size_t splits = 0;
            for (const auto &sat_values : sat_models)
                splits += refine_partition_with_values(
                    blocks, sat_values, output.statistics);
            if (splits == 0)
            {
                output.status = Status::Error;
                output.diagnostic =
                    "portfolio SAT model did not refine the partition";
                can_continue = false;
                break;
            }
            const std::vector<std::size_t> current_representatives =
                representatives(blocks, terms.size());
            for (const auto &[lhs, rhs] : certified_edges)
            {
                if (current_representatives.at(lhs) !=
                    current_representatives.at(rhs))
                {
                    output.status = Status::Error;
                    output.diagnostic =
                        "SAT model split an UNSAT-certified edge";
                    can_continue = false;
                    break;
                }
            }
        }
        else if (!all_edges_certified())
        {
            output.status = Status::Unknown;
            output.diagnostic =
                global_unknown
                    ? "global Z3 leader returned unknown before edge "
                      "certificates covered the epoch"
                    : "portfolio ended without SAT progress or complete "
                      "UNSAT certificates";
            can_continue = false;
        }

        if (log)
        {
            LOG_INFO(
                *log, "eqpartition",
                "global-edge BPR epoch=" +
                    std::to_string(output.statistics.parallel_rounds) +
                    " blocks=" + std::to_string(blocks.size()) +
                    " certified-edges=" +
                    std::to_string(certified_edges.size()) +
                    " canceled=" +
                    std::to_string(
                        output.statistics.parallel_canceled_checks) +
                    " winner=" + winning_task);
            log->flush();
        }
    }

    if (can_continue && output.status == Status::Error)
        output.status = Status::Complete;
    finalize_result(output, std::move(blocks));
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
    // An UNSAT worker query certifies every representative-star edge in that
    // query, not an entire block.  Edge-level certificates let one large block
    // be divided among workers without prematurely declaring the other chunks
    // equal.  They remain globally valid across later SAT refinements.
    std::set<ParallelEdge> certified_edges;

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
    const std::string fallback_base_smt =
        options.parallel_fallback == ParallelFallbackBackend::Bitwuzla ||
                options.parallel_embedded_global_fallback ==
                    ParallelFallbackBackend::Bitwuzla
            ? qfbv_smt2_base(constraints, terms)
            : std::string();
    if (can_continue && has_non_singleton(blocks))
    {
        apply_deterministic_seed_models(
            context, constraints, terms, blocks,
            output.statistics, log);
        workers.reserve(options.parallel_workers);
        for (std::size_t i = 0; i < options.parallel_workers; ++i)
            workers.push_back(std::make_unique<ParallelWorkerState>(
                context, constraints, terms));

    }

    while (can_continue)
    {
        std::vector<std::size_t> active_blocks;
        std::vector<ParallelEdge> active_edges;
        for (std::size_t i = 0; i < blocks.size(); ++i)
        {
            const auto &block = blocks[i];
            if (block.size() < 2)
                continue;
            const std::size_t representative = block.front();
            const std::size_t first_edge = active_edges.size();
            for (std::size_t j = 1; j < block.size(); ++j)
            {
                const ParallelEdge edge =
                    ordered_edge(representative, block[j]);
                if (!certified_edges.contains(edge))
                    active_edges.push_back(edge);
            }
            if (active_edges.size() != first_edge)
                active_blocks.push_back(i);
        }
        if (active_edges.empty())
            break;

        std::vector<std::vector<ParallelEdge>> assignments(
            options.parallel_workers);
        std::vector<std::size_t> loads(options.parallel_workers, 0);
        if (active_edges.size() < options.parallel_workers)
        {
            // Use otherwise-idle workers as a deterministic seed portfolio on
            // the remaining hard edges. The epoch is still synchronous: all
            // portfolio results are merged only after every query returns or
            // reaches the per-query timeout.
            for (std::size_t i = 0; i < options.parallel_workers; ++i)
            {
                assignments[i].push_back(
                    active_edges[i % active_edges.size()]);
                loads[i] = 1;
            }
        }
        else for (const ParallelEdge &edge : active_edges)
        {
            const auto target = std::min_element(
                loads.begin(), loads.end());
            const std::size_t worker_index =
                static_cast<std::size_t>(target - loads.begin());
            assignments[worker_index].push_back(edge);
            ++loads[worker_index];
        }

        std::size_t active_queries = 0;
        for (const auto &assignment : assignments)
            if (!assignment.empty())
                ++active_queries;
        ++output.statistics.parallel_rounds;
        output.statistics.max_parallel_queries = std::max(
            output.statistics.max_parallel_queries, active_queries);

        if (log)
        {
            std::ostringstream load_summary;
            for (std::size_t i = 0; i < loads.size(); ++i)
            {
                if (i != 0)
                    load_summary << ',';
                load_summary << loads[i];
            }
            LOG_INFO(
                *log, "eqpartition",
                "parallel BPR round-start=" +
                    std::to_string(output.statistics.parallel_rounds) +
                    " active-blocks=" +
                    std::to_string(active_blocks.size()) +
                    " queries=" + std::to_string(active_queries) +
                    " edge-loads=[" + load_summary.str() + "]");
            log->flush();
        }

        std::vector<ParallelQueryResult> primary_results(
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
                primary_results[i] = run_parallel_group_query(
                    *workers.at(i), assignments[i],
                    round_seed * static_cast<unsigned>(
                                     options.parallel_workers) +
                        static_cast<unsigned>(i) + 1,
                    options.parallel_query_timeout_ms);
            });
        }
        for (std::thread &thread : threads)
            thread.join();

        std::vector<ParallelQueryResult> query_results = primary_results;
        std::vector<bool> fallback_used(options.parallel_workers, false);
        threads.clear();
        if (options.parallel_fallback !=
            ParallelFallbackBackend::None)
        {
            std::vector<std::unique_ptr<NativePartitionWorker>>
                fallback_workers(options.parallel_workers);
            for (std::size_t i = 0; i < assignments.size(); ++i)
            {
                if (assignments[i].empty() ||
                    primary_results[i].outcome !=
                        ParallelQueryOutcome::Unknown)
                    continue;
                fallback_used[i] = true;
                if (options.parallel_fallback ==
                    ParallelFallbackBackend::Boolector)
                    fallback_workers[i] =
                        std::make_unique<BoolectorPartitionWorker>(
                            context, constraints, terms,
                            options.parallel_query_timeout_ms, i);
                else
                    fallback_workers[i] =
                        std::make_unique<BitwuzlaPartitionWorker>(
                            fallback_base_smt, terms,
                            options.parallel_query_timeout_ms, i);
            }
            for (std::size_t i = 0; i < assignments.size(); ++i)
            {
                if (!fallback_used[i])
                    continue;
                threads.emplace_back([&, i] {
                    query_results[i] =
                        fallback_workers[i]->check(assignments[i]);
                });
            }
            for (std::thread &thread : threads)
                thread.join();
        }

        std::size_t round_sat = 0;
        std::size_t round_unsat = 0;
        std::size_t round_unknown = 0;
        bool round_failed = false;
        for (std::size_t i = 0; i < assignments.size(); ++i)
        {
            if (assignments[i].empty())
                continue;
            const ParallelQueryResult &primary = primary_results[i];
            ++output.statistics.checks;
            output.statistics.check_time += primary.check_time;
            output.statistics.splitter_edges += primary.splitter_edges;
            output.statistics.max_splitter_edges = std::max(
                output.statistics.max_splitter_edges,
                primary.splitter_edges);
            if (primary.outcome == ParallelQueryOutcome::Sat)
                ++output.statistics.sat_checks;
            else if (primary.outcome == ParallelQueryOutcome::Unsat)
                ++output.statistics.unsat_checks;
            else if (primary.outcome == ParallelQueryOutcome::Unknown)
                ++output.statistics.parallel_unknown_checks;
            else
            {
                round_failed = true;
                output.status = Status::Error;
                output.diagnostic =
                    "parallel Z3 worker " + std::to_string(i) + ": " +
                    (primary.diagnostic.empty()
                         ? std::string("query failed")
                         : primary.diagnostic);
                break;
            }

            const ParallelQueryResult &query = query_results[i];
            if (fallback_used[i])
            {
                ++output.statistics.checks;
                ++output.statistics.parallel_fallback_checks;
                output.statistics.check_time += query.check_time;
                output.statistics.parallel_fallback_time += query.check_time;
                output.statistics.splitter_edges += query.splitter_edges;
                output.statistics.max_splitter_edges = std::max(
                    output.statistics.max_splitter_edges,
                    query.splitter_edges);
                if (query.outcome == ParallelQueryOutcome::Sat)
                {
                    ++output.statistics.sat_checks;
                    ++output.statistics.parallel_fallback_sat;
                }
                else if (query.outcome == ParallelQueryOutcome::Unsat)
                {
                    ++output.statistics.unsat_checks;
                    ++output.statistics.parallel_fallback_unsat;
                }
                else if (query.outcome == ParallelQueryOutcome::Unknown)
                {
                    ++output.statistics.parallel_unknown_checks;
                    ++output.statistics.parallel_fallback_unknown;
                }
                else
                {
                    round_failed = true;
                    output.status = Status::Error;
                    output.diagnostic =
                        std::string(parallel_fallback_name(
                            options.parallel_fallback)) +
                        " fallback worker " + std::to_string(i) + ": " +
                        (query.diagnostic.empty()
                             ? std::string("query failed")
                             : query.diagnostic);
                    break;
                }
            }
            if (query.outcome == ParallelQueryOutcome::Sat)
            {
                ++round_sat;
            }
            else if (query.outcome == ParallelQueryOutcome::Unsat)
            {
                ++round_unsat;
                for (const ParallelEdge &edge : assignments[i])
                    certified_edges.insert(edge);
            }
            else if (query.outcome == ParallelQueryOutcome::Unknown)
            {
                ++round_unknown;
            }
            else
            {
                round_failed = true;
                output.status = Status::Error;
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
        if (round_unknown != 0 &&
            round_unknown * 2 >= active_queries &&
            (options.parallel_boolector_global_fallback ||
             options.parallel_embedded_global_fallback !=
                 ParallelFallbackBackend::None))
        {
            const auto fallback_started = clk::now();
            const unsigned fallback_seconds = std::max(
                30u,
                options.parallel_query_timeout_ms == 0
                    ? 120u
                    : (options.parallel_query_timeout_ms / 1000u) * 4u);
            std::string fallback_result = "none";
            if (options.parallel_boolector_global_fallback)
            {
                const std::vector<z3::expr> inputs =
                    free_bv_inputs(constraints);
                const auto input_values = run_boolector_sat_witness(
                    constraints, inputs, active_edges, terms,
                    fallback_seconds);
                if (input_values)
                {
                    const auto model_values = validate_global_input_witness(
                        context, constraints, terms, {}, inputs,
                        *input_values, 10000u);
                    if (model_values)
                    {
                        fallback_result = "sat-validated";
                        ++output.statistics.checks;
                        ++output.statistics.sat_checks;
                        ++output.statistics.parallel_fallback_checks;
                        ++output.statistics.parallel_fallback_sat;
                        ++round_sat;
                        round_splits += refine_partition_with_values(
                            blocks, *model_values, output.statistics);
                    }
                }
            }
            else
            {
                const std::vector<z3::expr> inputs =
                    free_bv_inputs(constraints);
                std::vector<z3::expr> native_model_terms = terms;
                native_model_terms.insert(
                    native_model_terms.end(), inputs.begin(), inputs.end());
                const std::uint64_t timeout_ms_64 =
                    static_cast<std::uint64_t>(fallback_seconds) * 1000u;
                const unsigned fallback_timeout_ms =
                    static_cast<unsigned>(std::min<std::uint64_t>(
                        timeout_ms_64,
                        std::numeric_limits<unsigned>::max()));
                ParallelQueryResult query;
                if (options.parallel_embedded_global_fallback ==
                    ParallelFallbackBackend::Boolector)
                    query = run_boolector_parser_global_witness(
                        constraints, inputs, active_edges, terms,
                        fallback_timeout_ms);
                else
                {
                    std::unique_ptr<NativePartitionWorker> fallback_worker =
                        std::make_unique<BitwuzlaPartitionWorker>(
                            fallback_base_smt, native_model_terms,
                            fallback_timeout_ms,
                            output.statistics.parallel_rounds);
                    query = fallback_worker->check(active_edges);
                }
                ++output.statistics.checks;
                ++output.statistics.parallel_fallback_checks;
                output.statistics.splitter_edges +=
                    query.splitter_edges;
                output.statistics.max_splitter_edges = std::max(
                    output.statistics.max_splitter_edges,
                    query.splitter_edges);
                if (query.outcome == ParallelQueryOutcome::Sat)
                {
                    ++output.statistics.sat_checks;
                    std::optional<std::vector<std::string>> model_values;
                    std::vector<std::string> input_values;
                    if (options.parallel_embedded_global_fallback ==
                            ParallelFallbackBackend::Boolector &&
                        query.values.size() == inputs.size())
                        input_values = query.values;
                    else if (query.values.size() ==
                             native_model_terms.size())
                    {
                        const auto input_values_begin =
                            query.values.begin() +
                            static_cast<std::ptrdiff_t>(terms.size());
                        input_values.assign(
                            input_values_begin, query.values.end());
                    }
                    if (input_values.size() == inputs.size())
                    {
                        ++output.statistics.checks;
                        model_values = validate_global_input_witness(
                            context, constraints, terms, {},
                            inputs, input_values, 10000u);
                    }
                    if (model_values)
                    {
                        fallback_result = "sat-z3-completed";
                        ++output.statistics.sat_checks;
                        ++output.statistics.parallel_fallback_sat;
                        ++round_sat;
                        round_splits += refine_partition_with_values(
                            blocks, *model_values, output.statistics);
                    }
                    else
                    {
                        fallback_result = "sat-z3-rejected";
                        ++output.statistics.parallel_unknown_checks;
                        ++output.statistics.parallel_fallback_unknown;
                    }
                }
                else if (query.outcome == ParallelQueryOutcome::Unsat)
                {
                    fallback_result = "unsat-certified";
                    ++output.statistics.unsat_checks;
                    ++output.statistics.parallel_fallback_unsat;
                    ++round_unsat;
                    certified_edges.insert(
                        active_edges.begin(), active_edges.end());
                }
                else if (query.outcome == ParallelQueryOutcome::Unknown)
                {
                    fallback_result = "unknown";
                    ++output.statistics.parallel_unknown_checks;
                    ++output.statistics.parallel_fallback_unknown;
                }
                else
                {
                    output.status = Status::Error;
                    output.diagnostic =
                        std::string(parallel_fallback_name(
                            options.parallel_embedded_global_fallback)) +
                        " embedded global fallback: " +
                        (query.diagnostic.empty()
                             ? std::string("query failed")
                             : query.diagnostic);
                    can_continue = false;
                }
            }
            const auto fallback_elapsed =
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                    clk::now() - fallback_started);
            output.statistics.check_time += fallback_elapsed;
            output.statistics.parallel_fallback_time += fallback_elapsed;
            if (log)
                LOG_INFO(
                    *log, "eqpartition",
                    "parallel BPR global fallback backend=" +
                        (options.parallel_boolector_global_fallback
                             ? std::string("boolector-external")
                             : std::string(parallel_fallback_name(
                                   options.parallel_embedded_global_fallback))) +
                        " result=" + fallback_result +
                        " edges=" + std::to_string(active_edges.size()) +
                        " timeout-s=" +
                        std::to_string(fallback_seconds) +
                        " elapsed=" +
                        util::fmt_duration(fallback_elapsed));
            if (!can_continue)
                break;
        }
        if (round_sat != 0 && round_splits == 0)
            throw std::runtime_error(
                "parallel BPR SAT round did not refine the partition");

        const std::vector<std::size_t> current_representatives =
            representatives(blocks, terms.size());
        for (const auto &[lhs, rhs] : certified_edges)
        {
            if (current_representatives.at(lhs) !=
                current_representatives.at(rhs))
                throw std::runtime_error(
                    "parallel BPR model split an UNSAT-certified edge");
        }

        if (round_sat == 0 && round_unsat == 0)
        {
            output.status = Status::Unknown;
            output.diagnostic = "all parallel BPR queries returned unknown";
            can_continue = false;
            break;
        }

        if (log)
        {
            for (std::size_t i = 0; i < assignments.size(); ++i)
            {
                if (assignments[i].empty())
                    continue;
                const ParallelQueryResult &query = query_results[i];
                const char *result_name =
                    query.outcome == ParallelQueryOutcome::Sat
                        ? "sat"
                        : query.outcome == ParallelQueryOutcome::Unsat
                              ? "unsat"
                              : query.outcome == ParallelQueryOutcome::Unknown
                                    ? "unknown"
                                    : "error";
                std::string edge_detail;
                if (assignments[i].size() == 1)
                {
                    const auto &[lhs, rhs] = assignments[i].front();
                    edge_detail = " edge=(" +
                                  terms.at(lhs).to_string() + " != " +
                                  terms.at(rhs).to_string() + ")";
                }
                LOG_INFO(
                    *log, "eqpartition",
                    "parallel BPR worker=" + std::to_string(i) +
                        " round=" +
                        std::to_string(output.statistics.parallel_rounds) +
                        " result=" + result_name +
                        (fallback_used[i]
                             ? " fallback=" +
                                   std::string(parallel_fallback_name(
                                       options.parallel_fallback))
                             : std::string()) +
                        " edges=" +
                        std::to_string(assignments[i].size()) +
                        " elapsed=" +
                        util::fmt_duration(query.check_time) +
                        edge_detail);
            }
            LOG_INFO(
                *log, "eqpartition",
                "parallel BPR round=" +
                    std::to_string(
                        output.statistics.parallel_rounds) +
                    " queries=" + std::to_string(active_queries) +
                    " sat=" + std::to_string(round_sat) +
                    " unsat=" + std::to_string(round_unsat) +
                    " unknown=" + std::to_string(round_unknown) +
                    " blocks=" + std::to_string(blocks.size()) +
                    " certified-edges=" +
                    std::to_string(certified_edges.size()));
            log->flush();
        }
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
        " parallel-unknown=" +
        std::to_string(output.statistics.parallel_unknown_checks) +
        " query-timeout-ms=" +
        std::to_string(options.parallel_query_timeout_ms) +
        " fallback=" +
        std::string(parallel_fallback_name(options.parallel_fallback)) +
        " global-boolector-witness=" +
        (options.parallel_boolector_global_fallback ? "true" : "false") +
        " embedded-global-fallback=" +
        std::string(parallel_fallback_name(
            options.parallel_embedded_global_fallback)) +
        " fallback-checks=" +
        std::to_string(output.statistics.parallel_fallback_checks) +
        " fallback-sat=" +
        std::to_string(output.statistics.parallel_fallback_sat) +
        " fallback-unsat=" +
        std::to_string(output.statistics.parallel_fallback_unsat) +
        " fallback-unknown=" +
        std::to_string(output.statistics.parallel_fallback_unknown) +
        " final-global-validation=" +
        (options.parallel_final_global_validation ? "true" : "false");
    if (output.diagnostic.empty())
        output.diagnostic = parallel_diagnostic;
    else
        output.diagnostic += " " + parallel_diagnostic;
    finalize_result(output, std::move(blocks));
    return output;
}

Result run_hipr(z3::context &context,
                const std::vector<z3::expr> &constraints,
                const std::vector<z3::expr> &terms,
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
                         variant_name(Variant::Hipr) +
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

NativeSingletonValidationResult run_native_bv1_singleton_queries(
    z3::context &source_context,
    const std::vector<z3::expr> &source_constraints,
    const std::vector<z3::expr> &source_candidates,
    NativeSingletonBackend backend,
    std::size_t workers,
    unsigned timeout_ms,
    util::Logger *log)
{
    if (workers == 0)
        throw std::runtime_error(
            "native BV1 singleton validation requires at least one worker");
    for (const z3::expr &candidate : source_candidates)
        if (!candidate.get_sort().is_bv() ||
            candidate.get_sort().bv_size() != 1)
            throw std::runtime_error(
                "native BV1 singleton validation received a non-BV1 term");

    NativeSingletonValidationResult output;
    output.outcomes.resize(
        source_candidates.size(), NativeSingletonOutcome::Unknown);
    if (source_candidates.empty())
        return output;

    const auto all_started = clk::now();
    const z3::expr zero = source_context.bv_val(0, 1);
    const std::vector<z3::expr> declaration_terms = [&]() {
        std::vector<z3::expr> terms = source_candidates;
        terms.push_back(zero);
        return terms;
    }();
    const std::string bitwuzla_base =
        backend == NativeSingletonBackend::Bitwuzla
            ? qfbv_smt2_base(source_constraints, declaration_terms)
            : std::string();

    // Build each batch on the caller thread because Boolector's hand AST
    // translator reads the source Z3 context. The expensive SAT calls then run
    // concurrently, and every candidate gets a fresh solver so a timeout
    // cannot poison later singleton queries.
    for (std::size_t begin = 0; begin < source_candidates.size();
         begin += workers)
    {
        const std::size_t count = std::min(
            workers, source_candidates.size() - begin);
        std::vector<std::unique_ptr<NativePartitionWorker>> batch;
        batch.reserve(count);
        for (std::size_t offset = 0; offset < count; ++offset)
        {
            const std::vector<z3::expr> query_terms{
                source_candidates[begin + offset], zero};
            if (backend == NativeSingletonBackend::Boolector)
                batch.push_back(std::make_unique<BoolectorPartitionWorker>(
                    source_context, source_constraints, query_terms,
                    timeout_ms, begin + offset, true));
            else
                batch.push_back(std::make_unique<BitwuzlaPartitionWorker>(
                    bitwuzla_base, query_terms, timeout_ms,
                    begin + offset));
        }

        std::vector<ParallelQueryResult> results(count);
        std::vector<std::thread> threads;
        threads.reserve(count);
        for (std::size_t offset = 0; offset < count; ++offset)
            threads.emplace_back([&, offset]() {
                results[offset] = batch[offset]->check({{0, 1}});
            });
        for (std::thread &thread : threads)
            thread.join();

        for (std::size_t offset = 0; offset < count; ++offset)
        {
            const std::size_t candidate_index = begin + offset;
            const ParallelQueryResult &result = results[offset];
            ++output.checks;
            const char *status = "unknown";
            if (result.outcome == ParallelQueryOutcome::Sat)
            {
                output.outcomes[candidate_index] =
                    NativeSingletonOutcome::Sat;
                ++output.sat;
                status = "sat";
            }
            else if (result.outcome == ParallelQueryOutcome::Unsat)
            {
                output.outcomes[candidate_index] =
                    NativeSingletonOutcome::Unsat;
                ++output.unsat;
                status = "unsat";
            }
            else
                ++output.unknown;
            if (log)
                LOG_INFO(
                    *log, "eqpartition",
                    "BV1 singleton native query: backend=" +
                        std::string(
                            backend == NativeSingletonBackend::Boolector
                                ? "boolector"
                                : "bitwuzla") +
                        " term=" + source_candidates[candidate_index].to_string() +
                        " status=" + status +
                        " time=" + util::fmt_duration(result.check_time) +
                        (result.diagnostic.empty()
                             ? std::string()
                             : " detail=" + result.diagnostic));
        }
    }

    output.elapsed =
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            clk::now() - all_started);
    return output;
}

const char *variant_name(Variant variant)
{
    switch (variant)
    {
    case Variant::Z3Mpm:
        return "z3-mpm";
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
    case Variant::Bitwuzla:
        return "bitwuzla";
    case Variant::Boolector:
        return "boolector";
    case Variant::ParallelBpr:
        return "parallel-bpr";
    }
    return "unknown";
}

const char *parallel_fallback_name(ParallelFallbackBackend backend)
{
    switch (backend)
    {
    case ParallelFallbackBackend::None:
        return "none";
    case ParallelFallbackBackend::Boolector:
        return "boolector";
    case ParallelFallbackBackend::Bitwuzla:
        return "bitwuzla";
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
        else if (variant == Variant::Bitwuzla)
        {
            if (options.parallel_workers == 1)
                output = run_bitwuzla_partition(
                    constraints, terms,
                    options.parallel_query_timeout_ms, log);
            else
                output = run_native_parallel_partition(
                    context, constraints, terms, variant, options, log);
        }
        else if (variant == Variant::Boolector)
            output = run_native_parallel_partition(
                context, constraints, terms, variant, options, log);
        else if (variant == Variant::ParallelBpr)
        {
            const bool legacy_scheduler_requested =
                options.parallel_boolector_global_fallback ||
                options.parallel_embedded_global_fallback !=
                    ParallelFallbackBackend::None ||
                options.parallel_fallback !=
                    ParallelFallbackBackend::None ||
                options.parallel_final_global_validation;
            // Rebuilding and canceling several complete solver contexts per
            // epoch dominates large, model-friendly partitions (notably the
            // Kyber cuts).  Their persistent edge scheduler has bounded state
            // duplication and much better throughput.  Smaller formulas retain
            // the asynchronous global/native portfolio that avoids hard-edge
            // barriers.  Both schedulers require complete certificates and use
            // no production correctness timeout.
            constexpr std::size_t LARGE_PROBLEM_FOOTPRINT = 2048;
            const std::size_t problem_footprint =
                source_constraints.size() + source_terms.size();
            const bool persistent_scheduler_selected =
                options.parallel_scheduler ==
                    ParallelScheduler::Persistent ||
                (options.parallel_scheduler == ParallelScheduler::Auto &&
                 problem_footprint >= LARGE_PROBLEM_FOOTPRINT);
            if (log)
            {
                const char *scheduler_name =
                    legacy_scheduler_requested
                        ? "persistent-edge-legacy"
                        : persistent_scheduler_selected
                              ? "persistent-edge"
                              : "global-edge-portfolio";
                LOG_INFO(
                    *log, "eqpartition",
                    std::string("scheduler=") + scheduler_name +
                        " selection=" +
                        (options.parallel_scheduler ==
                                 ParallelScheduler::Auto
                             ? "auto"
                             : "forced") +
                        " footprint=" +
                        std::to_string(problem_footprint) +
                        " threshold=" +
                        std::to_string(LARGE_PROBLEM_FOOTPRINT));
            }
            output = (legacy_scheduler_requested ||
                      persistent_scheduler_selected)
                         ? run_parallel_bpr(
                               context, constraints, terms,
                               options, log)
                         : run_global_edge_portfolio(
                               context, constraints, terms,
                               options, log);
        }
        else if (variant == Variant::Hipr)
            output = run_hipr(context, constraints, terms, log);
        else
            throw std::runtime_error("unsupported partition variant");
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
                     " parallel-unknown=" +
                     std::to_string(stats.parallel_unknown_checks) +
                     " parallel-canceled=" +
                     std::to_string(stats.parallel_canceled_checks) +
                     " parallel-stale=" +
                     std::to_string(stats.parallel_stale_checks) +
                     " global-sat-wins=" +
                     std::to_string(stats.global_sat_wins) +
                     " chunk-sat-wins=" +
                     std::to_string(stats.chunk_sat_wins) +
                     " global-unsat-wins=" +
                     std::to_string(stats.global_unsat_wins) +
                     " chunk-certificate-completions=" +
                     std::to_string(
                         stats.chunk_certificate_completions) +
                     " zero-singleton-checks=" +
                     std::to_string(stats.zero_singleton_checks) +
                     " zero-singleton-sat=" +
                     std::to_string(stats.zero_singleton_sat) +
                     " zero-singleton-unsat=" +
                     std::to_string(stats.zero_singleton_unsat) +
                     " zero-singleton-unknown=" +
                     std::to_string(stats.zero_singleton_unknown) +
                     " zero-singleton-time=" +
                     util::fmt_duration(stats.zero_singleton_time) +
                     " automatic-native-checks=" +
                     std::to_string(
                         stats.parallel_fallback_checks) +
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
