#include "util/auto_zero_lemmas.hpp"

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <optional>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "util/bv_eq.hpp"
#include "util/fmt_duration.hpp"
#include "util/live_global_eq_validator.hpp"

namespace util::autozero
{

using namespace z3;
using clk = std::chrono::steady_clock;

constexpr std::size_t BV1_ZERO_WORKERS = 4;
constexpr unsigned BV1_ZERO_TIMEOUT_MS = 30000;
constexpr std::size_t BV1_ZERO_BATCH_SIZE = 2;
constexpr std::size_t BV1_ZERO_CALLBACK_BATCH_SIZE = 1;
constexpr unsigned BV1_ZERO_CALLBACK_DISCOVERY_TIMEOUT_MS = 10000;

namespace
{

bool is_bv_to_int_app(const expr &e)
{
    if (!e.is_app() || !e.get_sort().is_int() || e.num_args() != 1 ||
        !e.arg(0).get_sort().is_bv())
        return false;
#ifdef Z3_OP_BV2INT
    if (e.decl().decl_kind() == Z3_OP_BV2INT)
        return true;
#endif
    const std::string name = e.decl().name().str();
    return name == "ubv_to_int" || name == "sbv_to_int" ||
           name == "bv2nat" || name == "bv2int";
}

void collect_conversion_bases(const expr &e,
                              std::unordered_set<Z3_ast> &out)
{
    if (is_bv_to_int_app(e))
        out.insert((Z3_ast)e);
    if (!e.is_app())
        return;
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_conversion_bases(e.arg(i), out);
}

void collect_projected_constraints(const expr &e, std::vector<expr> &out)
{
    // Match the equality partition prepass projection: recursively flatten
    // only positive AND nodes reached from an assertion root. At every other
    // node, retain the complete subtree only when it is Poly-free. In
    // particular, never extract descendants through OR, NOT, implication,
    // ITE, XOR, Boolean equality, or another non-positive context.
    if (e.is_app() && e.decl().decl_kind() == Z3_OP_AND)
    {
        for (unsigned i = 0; i < e.num_args(); ++i)
            collect_projected_constraints(e.arg(i), out);
        return;
    }
    if (!util::bveq::assertion_contains_poly(e))
        out.push_back(e);
}

void deduplicate_exprs_preserving_order(std::vector<expr> &expressions)
{
    std::unordered_set<Z3_ast> seen;
    auto out = expressions.begin();
    for (auto it = expressions.begin(); it != expressions.end(); ++it)
        if (seen.insert((Z3_ast)*it).second)
            *out++ = *it;
    expressions.erase(out, expressions.end());
}

bool numeral_is_zero(const expr &value)
{
    std::uint64_t numeral = 0;
    return Z3_get_numeral_uint64((Z3_context)value.ctx(), (Z3_ast)value,
                                 &numeral) &&
           numeral == 0;
}

struct Candidate
{
    expr bv_term;
    std::vector<std::string> base_keys;

    explicit Candidate(const expr &term) : bv_term(term) {}
};

struct EqPInjectionDecls
{
    std::optional<func_decl> pconst;
    std::optional<func_decl> eqp;
};

void collect_eqp_injection_decls(const expr &e, EqPInjectionDecls &decls)
{
    if (!e.is_app())
        return;
    const std::string name = e.decl().name().str();
    if (name == "PConst" && e.num_args() == 1)
        decls.pconst = e.decl();
    else if (name == "eqP" && e.num_args() == 2)
        decls.eqp = e.decl();
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_eqp_injection_decls(e.arg(i), decls);
}

expr apply_decl(const std::optional<func_decl> &declaration,
                const std::vector<expr> &args)
{
    if (!declaration)
        throw std::runtime_error(
            "auto-zero-lemmas missing declaration for eqP injection");
    return (*declaration)(static_cast<unsigned>(args.size()), args.data());
}

void sort_unique_exprs(std::vector<expr> &terms)
{
    std::sort(terms.begin(), terms.end(),
              [](const expr &lhs, const expr &rhs) {
                  return lhs.to_string() < rhs.to_string();
              });
    terms.erase(std::unique(terms.begin(), terms.end(),
                            [](const expr &lhs, const expr &rhs) {
                                return z3::eq(lhs, rhs);
                            }),
                terms.end());
}

class Bv1ZeroCallbackCollector : public user_propagator_base
{
    std::vector<expr> m_terms;
    expr m_zero;
    std::vector<expr> m_candidates;
    std::unordered_set<Z3_ast> m_seen;

    void initialize()
    {
        register_eq();
        for (const expr &term : m_terms)
            add(term);
        add(m_zero);
    }

    void record_zero_equality(const expr &zero_side,
                              const expr &candidate_side)
    {
        if (!zero_side.is_numeral() || !numeral_is_zero(zero_side) ||
            !candidate_side.is_const() || candidate_side.is_numeral() ||
            !candidate_side.get_sort().is_bv() ||
            candidate_side.get_sort().bv_size() != 1)
            return;
        if (m_seen.insert((Z3_ast)candidate_side).second)
            m_candidates.push_back(candidate_side);
    }

public:
    Bv1ZeroCallbackCollector(solver *solver,
                             const std::vector<expr> &terms,
                             const expr &zero)
        : user_propagator_base(solver), m_terms(terms), m_zero(zero)
    {
        initialize();
    }

    Bv1ZeroCallbackCollector(context &ctx,
                             const std::vector<expr> &terms,
                             const expr &zero)
        : user_propagator_base(ctx),
          m_zero(ctx, Z3_translate((Z3_context)zero.ctx(), (Z3_ast)zero,
                                   (Z3_context)ctx))
    {
        m_terms.reserve(terms.size());
        for (const expr &term : terms)
            m_terms.emplace_back(
                ctx, Z3_translate((Z3_context)term.ctx(), (Z3_ast)term,
                                  (Z3_context)ctx));
        initialize();
    }

    const std::vector<expr> &candidates() const { return m_candidates; }

    void push() override {}
    void pop(unsigned) override {}
    void final() override {}

    void eq(const expr &lhs, const expr &rhs) override
    {
        record_zero_equality(lhs, rhs);
        record_zero_equality(rhs, lhs);
    }

    user_propagator_base *fresh(context &ctx) override
    {
        return new Bv1ZeroCallbackCollector(ctx, m_terms, m_zero);
    }
};

std::vector<expr> discover_bv1_zero_callback_candidates(
    context &ctx, const std::vector<expr> &projected_constraints,
    util::Logger &log)
{
    std::unordered_set<Z3_ast> all_bv_constants;
    for (const expr &constraint : projected_constraints)
        util::bveq::collect_bv_constants(constraint, all_bv_constants);

    std::vector<expr> registered_terms;
    registered_terms.reserve(all_bv_constants.size());
    for (Z3_ast ast : all_bv_constants)
    {
        expr term(ctx, ast);
        if (term.get_sort().is_bv() && term.get_sort().bv_size() == 1)
            registered_terms.push_back(term);
    }
    sort_unique_exprs(registered_terms);

    expr zero = ctx.bv_val(0, 1);
    solver candidate_solver(ctx);
    candidate_solver.set("timeout",
                         BV1_ZERO_CALLBACK_DISCOVERY_TIMEOUT_MS);
    for (const expr &constraint : projected_constraints)
        candidate_solver.add(constraint);
    Bv1ZeroCallbackCollector collector(&candidate_solver, registered_terms,
                                       zero);

    const auto started = clk::now();
    const check_result status = candidate_solver.check();
    std::vector<expr> candidates = collector.candidates();
    sort_unique_exprs(candidates);
    LOG_INFO(log, "auto-zero-lemmas",
             "[auto-zero-lemmas] callback-summary registered=" +
                 std::to_string(registered_terms.size()) +
                 " solver-status=" +
                 std::string(status == sat
                                 ? "sat"
                                 : status == unsat ? "unsat" : "unknown") +
                 " observed-candidates=" +
                 std::to_string(candidates.size()) +
                 " timeout-ms=" +
                 std::to_string(BV1_ZERO_CALLBACK_DISCOVERY_TIMEOUT_MS) +
                 " time=" + util::fmt_duration(clk::now() - started));
    return candidates;
}

std::vector<expr> validate_bv1_zero_candidates(
    context &ctx, const std::vector<expr> &projected_constraints,
    const std::vector<expr> &candidates, std::size_t batch_size,
    const char *mode_name, util::Logger *log,
    SingletonZeroValidationResult *validation_result = nullptr,
    unsigned timeout_ms = BV1_ZERO_TIMEOUT_MS,
    std::size_t workers = BV1_ZERO_WORKERS,
    bool exact_queries = false)
{
    if (candidates.empty())
        return {};

    expr zero = ctx.bv_val(0, 1);
    std::vector<expr> validation_terms = candidates;
    const std::size_t zero_index = validation_terms.size();
    validation_terms.push_back(zero);

    util::eqgb::LiveValidatorOptions options;
    options.workers = workers;
    options.timeout_ms = timeout_ms;
    options.batch_size = batch_size;
    options.start_paused = true;
    options.seed_models = !exact_queries;
    options.share_counterexamples = !exact_queries;
    options.unified_queue = true;

    const auto started = clk::now();
    util::eqgb::LiveGlobalEqValidator validator(
        ctx, projected_constraints, validation_terms, options, nullptr);
    for (std::size_t i = 0; i < candidates.size(); ++i)
        validator.submit_direct_candidate(i, zero_index, 0);
    validator.release();
    validator.wait_until_idle();

    const std::vector<util::eqgb::ValidationResult> results =
        validator.drain_results();
    std::vector<expr> proved;
    for (const util::eqgb::ValidationResult &result : results)
    {
        const std::size_t candidate_index =
            result.lhs == zero_index ? result.rhs : result.lhs;
        if (candidate_index < candidates.size() &&
            result.status == util::eqgb::ValidationStatus::Proved)
            proved.push_back(candidates[candidate_index]);
    }

    const util::eqgb::LiveValidatorStatistics stats = validator.statistics();
    // If any seed check proves the projected constraints inconsistent, every
    // equality is vacuously implied.  Injecting those facts is sound but not
    // useful, and obscures whether zero discovery contributed to the proof.
    if (stats.seed_unsat != 0)
    {
        if (validation_result)
        {
            validation_result->candidates = candidates.size();
            validation_result->checks = stats.checks;
            validation_result->refuted = stats.refuted;
            validation_result->unknown = stats.unknown;
            validation_result->model_pruned = stats.model_pruned;
            validation_result->constraints_unsat = true;
            validation_result->elapsed =
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                    clk::now() - started);
        }
        if (log)
            LOG_INFO(*log, "auto-zero-lemmas",
                     "[auto-zero-lemmas] projected constraints are unsat; "
                     "skipping vacuous zero lemmas");
        return {};
    }

    sort_unique_exprs(proved);
    const auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
        clk::now() - started);
    if (validation_result)
    {
        validation_result->proved_terms = proved;
        validation_result->candidates = candidates.size();
        validation_result->checks = stats.checks;
        validation_result->refuted = stats.refuted;
        validation_result->unknown = stats.unknown;
        validation_result->model_pruned = stats.model_pruned;
        validation_result->elapsed = elapsed;
    }
    if (log)
    {
        for (const expr &term : proved)
            LOG_INFO(*log, "auto-zero-lemmas",
                     "[auto-zero-lemmas] proved-validation-zero: " +
                         term.to_string() + " == #b0");
        LOG_INFO(*log, "auto-zero-lemmas",
                 std::string("[auto-zero-lemmas] validation-summary mode=") +
                     mode_name + " candidates=" +
                     std::to_string(candidates.size()) +
                     " workers=" + std::to_string(options.workers) +
                     " batch=" + std::to_string(options.batch_size) +
                     " timeout-ms=" + std::to_string(options.timeout_ms) +
                     " checks=" + std::to_string(stats.checks) +
                     " proved=" + std::to_string(proved.size()) +
                     " refuted=" + std::to_string(stats.refuted) +
                     " unknown=" + std::to_string(stats.unknown) +
                     " pending=" + std::to_string(stats.pending) +
                     " seed-checks=" + std::to_string(stats.seed_checks) +
                     " seed-unsat=" + std::to_string(stats.seed_unsat) +
                     " seed-models=" + std::to_string(stats.seed_models) +
                     " model-pruned=" + std::to_string(stats.model_pruned) +
                     " time=" + util::fmt_duration(elapsed));
    }
    return proved;
}

std::vector<expr> collect_bv1_validation_candidates(
    context &ctx, const std::vector<expr> &projected_constraints,
    const std::vector<expr> &coefficient_terms)
{
    std::vector<expr> terms = coefficient_terms;
    std::unordered_set<Z3_ast> all_bv_constants;
    for (const expr &constraint : projected_constraints)
        util::bveq::collect_bv_constants(constraint, all_bv_constants);
    for (Z3_ast ast : all_bv_constants)
    {
        expr term(ctx, ast);
        if (term.is_const() && !term.is_numeral() &&
            term.get_sort().is_bv() && term.get_sort().bv_size() == 1)
            terms.push_back(term);
    }
    sort_unique_exprs(terms);
    return terms;
}

std::vector<expr> prove_bv1_zero_candidates(
    context &ctx, const std::vector<expr> &projected_constraints,
    const std::vector<Candidate> &coefficient_candidates,
    util::Logger &log,
    std::size_t &validation_candidate_count)
{
    std::vector<expr> coefficient_terms;
    coefficient_terms.reserve(coefficient_candidates.size());
    for (const Candidate &candidate : coefficient_candidates)
        coefficient_terms.push_back(candidate.bv_term);
    sort_unique_exprs(coefficient_terms);
    const std::vector<expr> terms = collect_bv1_validation_candidates(
        ctx, projected_constraints, coefficient_terms);
    validation_candidate_count = terms.size();
    if (terms.empty())
        return {};

    LOG_INFO(log, "auto-zero-lemmas",
             "[auto-zero-lemmas] zero-class-size=" +
                 std::to_string(terms.size() + 1) +
                 " validation-candidates=" +
                 std::to_string(terms.size()) +
                 " coefficient-targets=" +
                 std::to_string(coefficient_terms.size()) +
                 " extra-terms=" +
                 std::to_string(terms.size() - coefficient_terms.size()) +
                 " group-size=" +
                 std::to_string(BV1_ZERO_BATCH_SIZE));
    return validate_bv1_zero_candidates(
        ctx, projected_constraints, terms, BV1_ZERO_BATCH_SIZE,
        "grouped-zero-anchor", &log);
}

} // namespace

SingletonZeroValidationResult validate_bv1_singleton_zeros(
    context &ctx, const std::vector<expr> &projected_constraints,
    const std::vector<expr> &candidates, util::Logger *log,
    unsigned timeout_ms, std::size_t workers, bool exact_queries)
{
    SingletonZeroValidationResult result;
    result.candidates = candidates.size();
    if (candidates.empty())
        return result;
    (void)validate_bv1_zero_candidates(
        ctx, projected_constraints, candidates,
        BV1_ZERO_CALLBACK_BATCH_SIZE, "partition-bv1-singleton-zero",
        log, &result, timeout_ms, workers, exact_queries);
    return result;
}

Result discover_implied_zeros(context &ctx,
                              const std::vector<expr> &assertions,
                              DiscoveryMode mode,
                              util::Logger &log)
{
    const auto started = clk::now();
    Result result;

    std::vector<expr> projected_constraints;
    projected_constraints.reserve(assertions.size());
    for (const expr &assertion : assertions)
        collect_projected_constraints(assertion, projected_constraints);
    deduplicate_exprs_preserving_order(projected_constraints);

    std::unordered_set<Z3_ast> base_set;
    for (const expr &assertion : assertions)
        collect_conversion_bases(assertion, base_set);

    std::vector<Candidate> candidates;
    std::unordered_map<Z3_ast, std::size_t> candidate_by_term;
    for (Z3_ast ast : base_set)
    {
        expr base(ctx, ast);
        if (!is_bv_to_int_app(base))
            continue;
        expr term = base.arg(0);
        if (!term.is_const() || term.is_numeral())
            continue;
        // The discovery engine is specifically BV1. Wider conversions cannot
        // be proved or injected by this module.
        if (!term.get_sort().is_bv() || term.get_sort().bv_size() != 1)
            continue;

        auto [it, inserted] =
            candidate_by_term.emplace((Z3_ast)term, candidates.size());
        if (inserted)
            candidates.emplace_back(term);
        candidates[it->second].base_keys.push_back(base.to_string());
    }

    result.coefficient_target_count = candidates.size();
    LOG_INFO(log, "auto-zero-lemmas",
             "[auto-zero-lemmas] coefficient-targets=" +
                 std::to_string(result.coefficient_target_count) +
                 " projected-constraints=" +
                 std::to_string(projected_constraints.size()));
    if (candidates.empty())
        return result;

    std::vector<expr> proved_terms;
    if (mode == DiscoveryMode::Callback)
    {
        const std::vector<expr> callback_candidates =
            discover_bv1_zero_callback_candidates(
                ctx, projected_constraints, log);
        result.validation_candidate_count = callback_candidates.size();
        proved_terms = validate_bv1_zero_candidates(
            ctx, projected_constraints, callback_candidates,
            BV1_ZERO_CALLBACK_BATCH_SIZE, "callback", &log);
    }
    else
    {
        proved_terms = prove_bv1_zero_candidates(
            ctx, projected_constraints, candidates, log,
            result.validation_candidate_count);
    }
    std::vector<std::size_t> proved;
    for (const expr &term : proved_terms)
    {
        auto found = candidate_by_term.find((Z3_ast)term);
        if (found != candidate_by_term.end())
            proved.push_back(found->second);
    }

    std::sort(proved.begin(), proved.end());
    proved.erase(std::unique(proved.begin(), proved.end()), proved.end());
    for (std::size_t i : proved)
    {
        for (const std::string &base_key : candidates[i].base_keys)
        {
            result.implied_zero_bases.push_back(base_key);
            LOG_INFO(log, "auto-zero-lemmas",
                     "[auto-zero-lemmas] proved-coefficient-zero: " +
                         base_key);
        }
    }
    std::sort(result.implied_zero_bases.begin(),
              result.implied_zero_bases.end());
    result.implied_zero_bases.erase(
        std::unique(result.implied_zero_bases.begin(),
                    result.implied_zero_bases.end()),
        result.implied_zero_bases.end());

    LOG_INFO(log, "auto-zero-lemmas",
             "[auto-zero-lemmas] discovery-summary coefficient-zeros=" +
                 std::to_string(result.implied_zero_bases.size()) +
                 " time=" + util::fmt_duration(clk::now() - started));
    return result;
}

std::vector<expr> inject_as_eqp(context &ctx,
                                const std::vector<expr> &assertions,
                                const Result &result,
                                util::Logger &log)
{
    std::vector<expr> injected;
    if (result.implied_zero_bases.empty())
        return injected;

    EqPInjectionDecls decls;
    std::unordered_set<Z3_ast> base_set;
    std::unordered_set<std::string> existing_assertions;
    for (const expr &assertion : assertions)
    {
        collect_eqp_injection_decls(assertion, decls);
        collect_conversion_bases(assertion, base_set);
        existing_assertions.insert(assertion.to_string());
    }
    if (!decls.pconst && !decls.eqp)
    {
        const sort poly = ctx.uninterpreted_sort("Poly");
        decls.pconst = ctx.function("PConst", ctx.int_sort(), poly);
        decls.eqp = ctx.function("eqP", poly, poly, ctx.bool_sort());
    }
    else if (!decls.pconst)
    {
        const sort poly = decls.eqp->domain(0);
        decls.pconst = ctx.function("PConst", ctx.int_sort(), poly);
    }
    else if (!decls.eqp)
    {
        const sort poly = decls.pconst->range();
        decls.eqp = ctx.function("eqP", poly, poly, ctx.bool_sort());
    }

    std::unordered_map<std::string, Z3_ast> base_by_key;
    for (Z3_ast ast : base_set)
    {
        expr base(ctx, ast);
        if (is_bv_to_int_app(base))
            base_by_key.emplace(base.to_string(), ast);
    }

    std::unordered_set<std::string> emitted;
    std::size_t already_present = 0;
    for (const std::string &base_key : result.implied_zero_bases)
    {
        auto found = base_by_key.find(base_key);
        if (found == base_by_key.end())
            throw std::runtime_error(
                "auto-zero-lemmas cannot recover proved coefficient base: " +
                base_key);

        const expr base(ctx, found->second);
        const expr lhs_poly = apply_decl(decls.pconst, {base});
        const expr rhs_poly =
            apply_decl(decls.pconst, {ctx.int_val(0)});
        const expr eqp = apply_decl(decls.eqp, {lhs_poly, rhs_poly});
        const std::string key = eqp.to_string();
        if (existing_assertions.count(key) != 0)
        {
            ++already_present;
            continue;
        }
        if (!emitted.insert(key).second)
            continue;

        injected.push_back(eqp);
        LOG_INFO(log, "auto-zero-lemmas",
                 "[auto-zero-lemmas] injected globally proved zero as eqP: " +
                     key);
    }

    LOG_INFO(log, "auto-zero-lemmas",
             "[auto-zero-lemmas] injected-eqps=" +
                 std::to_string(injected.size()) +
                 " already-present=" + std::to_string(already_present));
    return injected;
}

} // namespace util::autozero
