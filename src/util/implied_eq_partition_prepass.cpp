#include "util/implied_eq_partition_prepass.hpp"

#include <algorithm>
#include <cstdint>
#include <iomanip>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <thread>
#include <unordered_map>

#include "util/auto_zero_lemmas.hpp"
#include <unordered_set>

#include "util/bv_to_int.hpp"
#include "util/fmt_duration.hpp"
#include "util/logger.hpp"

namespace util::eqpartition
{
namespace
{

// Both interpreted conversions map the zero bit-vector to 0.
bool is_semantic_bv_to_int_decl(
    z3::context &context, Z3_func_decl raw)
{
    return raw && is_interpreted_bv_to_int(z3::func_decl(context, raw));
}

bool is_bv_zero_numeral(const z3::expr &expression)
{
    if (!expression.is_numeral() || !expression.get_sort().is_bv())
        return false;
    std::uint64_t value = 0;
    return Z3_get_numeral_uint64(
               (Z3_context)expression.ctx(), (Z3_ast)expression, &value) &&
           value == 0;
}

bool assertion_contains_poly(const z3::expr &expression)
{
    if (!expression.is_app())
        return false;
    const std::string name = expression.decl().name().str();
    if (name == "eqP" || name == "eqmodP1" || name == "eqmodP2" ||
        name == "eqmodP3" || name == "eqmodP4" ||
        name == "PConst" || name == "PVar" || name == "PNeg" ||
        name == "PAdd" || name == "PSub" || name == "PMul" ||
        name == "PPow")
        return true;
    for (unsigned i = 0; i < expression.num_args(); ++i)
        if (assertion_contains_poly(expression.arg(i)))
            return true;
    return false;
}

void collect_projected_constraints(
    const z3::expr &expression,
    std::vector<z3::expr> &out)
{
    // An asserted positive conjunction implies each of its children, so it is
    // sound to flatten only AND nodes reached from the assertion root.  Do not
    // recurse through OR, NOT, implication, ITE, XOR, Boolean equality, or
    // other contexts: extracting a Poly-free descendant there could strengthen
    // the projection and make an injected equality unsound.
    if (expression.is_app() &&
        expression.decl().decl_kind() == Z3_OP_AND)
    {
        for (unsigned i = 0; i < expression.num_args(); ++i)
            collect_projected_constraints(expression.arg(i), out);
        return;
    }

    if (!assertion_contains_poly(expression))
        out.push_back(expression);
}

void collect_conversion_bases(const z3::expr &expression,
                              std::unordered_set<Z3_ast> &out)
{
    if (is_bv_to_int_app(expression))
        out.insert((Z3_ast)expression);
    if (!expression.is_app())
        return;
    for (unsigned i = 0; i < expression.num_args(); ++i)
        collect_conversion_bases(expression.arg(i), out);
}

struct InjectionDecls
{
    Z3_func_decl pconst = nullptr;
    Z3_func_decl eqp = nullptr;
};

void collect_injection_decls(const z3::expr &expression,
                             InjectionDecls &decls)
{
    if (!expression.is_app())
        return;
    const std::string name = expression.decl().name().str();
    if (name == "PConst" && expression.num_args() == 1)
        decls.pconst = (Z3_func_decl)expression.decl();
    else if (name == "eqP" && expression.num_args() == 2)
        decls.eqp = (Z3_func_decl)expression.decl();
    for (unsigned i = 0; i < expression.num_args(); ++i)
        collect_injection_decls(expression.arg(i), decls);
}

z3::expr apply_decl(z3::context &context, Z3_func_decl raw,
                    const std::vector<z3::expr> &arguments)
{
    if (!raw)
        throw std::runtime_error(
            "partition prepass is missing an eqP injection declaration");
    z3::func_decl declaration(context, raw);
    return declaration(static_cast<unsigned>(arguments.size()),
                       arguments.data());
}

struct TermInfo
{
    z3::expr term;
    std::vector<Z3_func_decl> conversions;

    explicit TermInfo(const z3::expr &value) : term(value) {}
};

std::string compact(const std::string &text)
{
    std::string result = text;
    std::replace(result.begin(), result.end(), '\n', ' ');
    return result;
}

std::string stable_digest(const std::string &text)
{
    std::uint64_t hash = 14695981039346656037ull;
    for (const unsigned char ch : text)
    {
        hash ^= ch;
        hash *= 1099511628211ull;
    }
    std::ostringstream out;
    out << "fnv1a64:" << std::hex << std::setfill('0') << std::setw(16)
        << hash;
    return out.str();
}

void canonicalize_complete_partition(
    PrepassResult &output,
    Result &result,
    const std::vector<z3::expr> &terms)
{
    result.proof_edges.clear();
    output.canonical_classes.clear();
    output.canonical_zero_terms.clear();

    for (const auto &block : result.classes)
    {
        if (block.empty())
            continue;

        std::vector<std::string> members;
        members.reserve(block.size());
        std::optional<std::size_t> zero_index;
        for (const std::size_t index : block)
        {
            if (index >= terms.size())
                throw std::runtime_error(
                    "partition result contains an invalid term index");
            members.push_back(
                terms[index].get_sort().to_string() + ":" +
                terms[index].to_string());
            if (is_bv_zero_numeral(terms[index]))
                zero_index = index;
        }
        std::sort(members.begin(), members.end());
        output.canonical_classes.push_back(std::move(members));

        if (block.size() < 2)
            continue;
        const std::size_t anchor = zero_index.value_or(block.front());
        for (const std::size_t index : block)
        {
            if (index != anchor)
                result.proof_edges.emplace_back(anchor, index);
        }
        if (zero_index)
        {
            for (const std::size_t index : block)
                if (index != *zero_index && !terms[index].is_numeral())
                    output.canonical_zero_terms.push_back(
                        terms[index].to_string());
        }
    }

    std::sort(output.canonical_classes.begin(),
              output.canonical_classes.end());
    std::sort(output.canonical_zero_terms.begin(),
              output.canonical_zero_terms.end());
    output.final_classes = output.canonical_classes.size();
    output.bv1_zero_count = output.canonical_zero_terms.size();
    output.bv1_zero_proved = output.bv1_zero_count;
    result.statistics.proof_edges = result.proof_edges.size();

    std::ostringstream classes;
    for (const auto &members : output.canonical_classes)
    {
        classes << '[';
        for (const std::string &member : members)
            classes << member.size() << ':' << member << ';';
        classes << ']';
    }
    std::ostringstream zeros;
    for (const std::string &member : output.canonical_zero_terms)
        zeros << member.size() << ':' << member << ';';
    output.class_digest = stable_digest(classes.str());
    output.zero_digest = stable_digest(zeros.str());
}

} // namespace

PrepassResult run_eqp_prepass(
    z3::context &context,
    const std::vector<z3::expr> &source_assertions,
    util::Logger *log)
{
    return run_eqp_prepass(context, source_assertions, PrepassOptions{}, log);
}

PrepassResult run_eqp_prepass(
    z3::context &context,
    const std::vector<z3::expr> &source_assertions,
    const PrepassOptions &prepass_options,
    util::Logger *log)
{
    PrepassResult output;
    std::vector<z3::expr> constraints;
    for (const z3::expr &assertion : source_assertions)
        collect_projected_constraints(assertion, constraints);
    output.constraints = constraints.size();

    std::unordered_set<Z3_ast> conversion_bases;
    InjectionDecls injection_decls;
    for (const z3::expr &assertion : source_assertions)
    {
        collect_conversion_bases(assertion, conversion_bases);
        collect_injection_decls(assertion, injection_decls);
    }

    std::vector<TermInfo> term_infos;
    std::unordered_map<Z3_ast, std::size_t> term_indices;
    for (Z3_ast raw_base : conversion_bases)
    {
        z3::expr base(context, raw_base);
        z3::expr term = base.arg(0);
        if (!term.get_sort().is_bv() || term.is_numeral())
            continue;
        auto [position, inserted] =
            term_indices.emplace((Z3_ast)term, term_infos.size());
        if (inserted)
            term_infos.emplace_back(term);
        auto &conversions = term_infos[position->second].conversions;
        const Z3_func_decl conversion = (Z3_func_decl)base.decl();
        if (std::find(conversions.begin(), conversions.end(), conversion) ==
            conversions.end())
            conversions.push_back(conversion);
    }

    std::sort(term_infos.begin(), term_infos.end(),
              [](const TermInfo &lhs, const TermInfo &rhs) {
                  return lhs.term.to_string() < rhs.term.to_string();
              });
    output.original_terms = term_infos.size();
    std::vector<TermInfo> bv1_term_infos;
    for (const TermInfo &info : term_infos)
    {
        if (info.term.get_sort().is_bv() &&
            info.term.get_sort().bv_size() == 1)
            bv1_term_infos.push_back(info);
    }
    output.bv1_zero_anchor_added =
        prepass_options.include_bv1_zero_anchor &&
        !bv1_term_infos.empty();
    output.bv1_zero_candidates = bv1_term_infos.size();
    if (output.bv1_zero_anchor_added &&
        !prepass_options.bv1_zero_only)
        term_infos.emplace_back(context.bv_val(0, 1));

    std::vector<z3::expr> terms;
    terms.reserve(term_infos.size());
    for (const TermInfo &info : term_infos)
        terms.push_back(info.term);
    output.anchor_terms =
        output.bv1_zero_anchor_added ? 1 : 0;
    output.terms = output.original_terms + output.anchor_terms;

    // Group 0 holds the terms read unsigned and group 1 those read signed, so
    // a term is only ever compared with terms read the same way.
    std::vector<unsigned> view_groups;
    if (prepass_options.split_by_view)
    {
        std::string together;
        if (prepass_options.lift_casts)
            together = "lift-casts needs equalities across the views";
        for (std::size_t i = 0; together.empty() && i < term_infos.size(); ++i)
        {
            const TermInfo &info = term_infos[i];
            if (is_bv_zero_numeral(info.term))
            {
                view_groups.push_back(0);
                continue;
            }
            if (info.conversions.size() != 1 ||
                !is_semantic_bv_to_int_decl(context, info.conversions.front()))
            {
                together = "a term does not have exactly one interpreted "
                           "conversion: " +
                           info.term.to_string();
                break;
            }
            const bool read_signed =
                z3::func_decl(context, info.conversions.front())
                    .decl_kind() == Z3_OP_SBV2INT;
            if (read_signed && info.term.get_sort().bv_size() == 1)
            {
                together = "a 1-bit term is read signed: " +
                           info.term.to_string();
                break;
            }
            view_groups.push_back(read_signed ? 1u : 0u);
        }
        if (!together.empty())
        {
            view_groups.clear();
            if (log)
                LOG_INFO(*log, "eqpartition",
                         "partition prepass keeps signed and unsigned terms "
                         "together: " +
                             together);
        }
    }
    output.split_by_view = !view_groups.empty();

    if (log)
    {
        LOG_INFO(*log, "eqpartition",
                 "partition prepass started: constraints=" +
                     std::to_string(constraints.size()) +
                     " terms=" + std::to_string(output.terms) +
                     " partition-terms=" + std::to_string(terms.size()) +
                     " bv1-zero-candidates=" +
                     std::to_string(bv1_term_infos.size()) +
                     " split-by-view=" +
                     (output.split_by_view ? "true" : "false"));
        log->flush();
    }

    util::autozero::SingletonZeroValidationResult zero_validation;
    auto run_zero_validation = [&]() {
        if (!output.bv1_zero_anchor_added)
            return;
        std::vector<z3::expr> bv1_candidates;
        bv1_candidates.reserve(bv1_term_infos.size());
        for (const TermInfo &info : bv1_term_infos)
            bv1_candidates.push_back(info.term);
        if (prepass_options.bv1_zero_backend == Bv1ZeroBackend::Z3)
            zero_validation = util::autozero::validate_bv1_singleton_zeros(
                context, constraints, bv1_candidates, log,
                prepass_options.bv1_zero_timeout_ms,
                prepass_options.bv1_zero_workers,
                prepass_options.bv1_zero_exact_queries);
        else
        {
            const NativeSingletonValidationResult native =
                run_native_bv1_singleton_queries(
                    context, constraints, bv1_candidates,
                    prepass_options.bv1_zero_workers,
                    prepass_options.bv1_zero_timeout_ms, log);
            zero_validation.candidates = bv1_candidates.size();
            zero_validation.checks = native.checks;
            zero_validation.refuted = native.sat;
            zero_validation.unknown = native.unknown;
            zero_validation.elapsed = native.elapsed;
            for (std::size_t i = 0; i < native.outcomes.size(); ++i)
                if (native.outcomes[i] == NativeSingletonOutcome::Unsat)
                    zero_validation.proved_terms.push_back(bv1_candidates[i]);
        }
        output.bv1_zero_candidates = zero_validation.candidates;
        output.bv1_zero_proved = zero_validation.proved_terms.size();
        output.bv1_zero_refuted = zero_validation.refuted;
        output.bv1_zero_unknown = zero_validation.unknown;
        output.bv1_zero_checks = zero_validation.checks;
        output.bv1_zero_elapsed = zero_validation.elapsed;
        if (log)
            log->flush();
    };

    Result selected_result;
    if (prepass_options.bv1_zero_only)
    {
        run_zero_validation();
        output.status = zero_validation.constraints_unsat
                            ? Status::Complete
                            : zero_validation.unknown == 0
                                  ? Status::Complete
                                  : Status::Unknown;
        if (output.status == Status::Unknown)
            output.diagnostic =
                "legacy BV1 singleton validation returned unknown";
        if (log)
        {
            const char *backend =
                prepass_options.bv1_zero_backend == Bv1ZeroBackend::Z3
                    ? "z3"
                    : "boolector";
            LOG_INFO(
                *log, "eqpartition",
                "BV1 zero-only benchmark summary: backend=" +
                    std::string(backend) +
                    " workers=" +
                    std::to_string(prepass_options.bv1_zero_workers) +
                    " candidates=" +
                    std::to_string(output.bv1_zero_candidates) +
                    " checks=" + std::to_string(output.bv1_zero_checks) +
                    " proved=" + std::to_string(output.bv1_zero_proved) +
                    " refuted=" + std::to_string(output.bv1_zero_refuted) +
                    " unknown=" + std::to_string(output.bv1_zero_unknown) +
                    " time=" + util::fmt_duration(output.bv1_zero_elapsed));
            log->flush();
        }
        return output;
    }
    if (prepass_options.experimental_variant)
    {
        VariantOptions variant_options;
        variant_options.parallel_workers =
            prepass_options.parallel_workers;
        variant_options.z3_only = prepass_options.z3_only;
        variant_options.parallel_scheduler =
            prepass_options.parallel_scheduler;
        variant_options.parallel_query_timeout_ms =
            prepass_options.parallel_query_timeout_ms;
        variant_options.parallel_boolector_global_fallback =
            prepass_options.parallel_boolector_global_fallback;
        variant_options.parallel_embedded_global_fallback =
            prepass_options.parallel_embedded_global_fallback;
        variant_options.parallel_fallback =
            prepass_options.parallel_fallback;
        variant_options.parallel_final_global_validation =
            prepass_options.parallel_final_global_validation;
        variant_options.initial_groups = view_groups;
        selected_result = run_variant(
            context, constraints, terms,
            *prepass_options.experimental_variant,
            variant_options, log);
    }
    else
    {
        Options options;
        options.timeout_ms = 0;
        options.start_async = false;
        options.initial_groups = view_groups;
        ImpliedEqualityPartitionRefiner refiner(
            context, constraints, terms, options, log);
        selected_result = refiner.wait();
    }
    Result &result = selected_result;
    output.status = result.status;
    output.diagnostic = result.diagnostic;
    output.partition_statistics = result.statistics;
    if (result.status != Status::Complete)
    {
        if (log)
            LOG_INFO(*log, "eqpartition",
                     "partition prepass failed closed: status=" +
                         std::string(status_name(result.status)) +
                         (result.diagnostic.empty()
                              ? std::string()
                              : " diagnostic=" + result.diagnostic));
        return output;
    }
    output.constraints_unsat = result.constraints_unsat;
    if (output.constraints_unsat)
    {
        result.classes.clear();
        result.proof_edges.clear();
        result.statistics.final_blocks = 0;
        result.statistics.equality_classes = 0;
        result.statistics.proof_edges = 0;
        result.statistics.implied_pairs = 0;
        output.class_digest = stable_digest("");
        output.zero_digest = stable_digest("");
    }
    else
        canonicalize_complete_partition(output, result, terms);
    output.partition_statistics = result.statistics;

    auto log_summary = [&]() {
        if (!log)
            return;
        const Statistics &stats = output.partition_statistics;
        LOG_INFO(*log, "eqpartition",
                 "partition prepass summary: status=complete constraints=" +
                     std::to_string(output.constraints) +
                     " original-term-count=" +
                     std::to_string(output.original_terms) +
                     " anchor-term-count=" +
                     std::to_string(output.anchor_terms) +
                     " terms=" + std::to_string(output.terms) +
                     " z3-only=" +
                     (prepass_options.z3_only ? "true" : "false") +
                     " scheduler=" +
                     (prepass_options.parallel_scheduler ==
                              ParallelScheduler::Auto
                          ? "auto"
                          : prepass_options.parallel_scheduler ==
                                    ParallelScheduler::Persistent
                                ? "persistent"
                                : "portfolio") +
                     " bv1-zero-anchor=" +
                     (output.bv1_zero_anchor_added ? "true" : "false") +
                     " bv1-zero-mode=" +
                     (output.bv1_zero_anchor_added
                          ? "unified-partition"
                          : "disabled") +
                     " bv1-zero-backend=" +
                     (prepass_options.bv1_zero_backend == Bv1ZeroBackend::Z3
                          ? "z3"
                          : "boolector") +
                     " bv1-zero-workers=" +
                     std::to_string(prepass_options.bv1_zero_workers) +
                     " widths-concurrent=" +
                     (prepass_options.concurrent_widths
                          ? "true"
                          : "false") +
                     " bv1-zero-candidates=" +
                     std::to_string(output.bv1_zero_candidates) +
                     " bv1-zero-proved=" +
                     std::to_string(output.bv1_zero_count) +
                     " bv1-zero-count=" +
                     std::to_string(output.bv1_zero_count) +
                     " bv1-zero-refuted=" +
                     std::to_string(output.bv1_zero_refuted) +
                     " bv1-zero-unknown=" +
                     std::to_string(output.bv1_zero_unknown) +
                     " bv1-zero-checks=" +
                     std::to_string(output.bv1_zero_checks) +
                     " bv1-zero-time=" +
                     util::fmt_duration(output.bv1_zero_elapsed) +
                     " constraints-unsat=" +
                     (output.constraints_unsat ? "true" : "false") +
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
                     " automatic-native-sat=" +
                     std::to_string(
                         stats.parallel_fallback_sat) +
                     " automatic-native-unsat=" +
                     std::to_string(
                         stats.parallel_fallback_unsat) +
                     " automatic-native-unknown=" +
                     std::to_string(
                         stats.parallel_fallback_unknown) +
                     " final-validation-checks=" +
                     std::to_string(stats.final_validation_checks) +
                     " final-validation-time=" +
                     util::fmt_duration(stats.final_validation_time) +
                     " equality-classes=" +
                     std::to_string(stats.equality_classes) +
                     " final-classes=" +
                     std::to_string(output.final_classes) +
                     " proof-edges=" +
                     std::to_string(stats.proof_edges) +
                     " implied-pairs=" +
                     std::to_string(stats.implied_pairs) +
                     " class-digest=" + output.class_digest +
                     " zero-digest=" + output.zero_digest +
                     " injection-mode=" +
                     (prepass_options.inject_all_pairs
                          ? "all-pairs"
                          : "proof-forest") +
                     " injected-eqps=" +
                     std::to_string(output.injected_eqps) +
                     " cross-view-edges=" +
                     std::to_string(output.cross_view_edges) +
                     " cross-view-lifted=" +
                     std::to_string(output.cross_view_lifted) +
                     " split-by-view=" +
                     (output.split_by_view ? "true" : "false") +
                     " check-time=" +
                     util::fmt_duration(stats.check_time) +
                     " elapsed=" + util::fmt_duration(stats.elapsed));
    };

    if (output.constraints_unsat)
    {
        if (log)
            LOG_INFO(*log, "eqpartition",
                     "partition prepass skipped equality injection because "
                     "the non-Poly constraints are UNSAT");
        log_summary();
        return output;
    }

    if (output.bv1_zero_count != 0)
    {
        for (const auto &block : result.classes)
        {
            const bool contains_zero = std::any_of(
                block.begin(), block.end(),
                [&](const std::size_t index) {
                    return is_bv_zero_numeral(terms.at(index));
                });
            if (!contains_zero)
                continue;
            for (const std::size_t index : block)
            {
                if (is_bv_zero_numeral(terms.at(index)))
                    continue;
                const auto &conversions =
                    term_infos.at(index).conversions;
                if (std::none_of(
                        conversions.begin(), conversions.end(),
                        [&](const Z3_func_decl conversion) {
                            return is_semantic_bv_to_int_decl(
                                context, conversion);
                        }))
                {
                    output.status = Status::Error;
                    output.diagnostic =
                        "zero-anchor member has no semantic BV-to-Int "
                        "conversion: " +
                        terms.at(index).to_string();
                    if (log)
                        LOG_INFO(
                            *log, "eqpartition",
                            "partition prepass failed closed: " +
                                output.diagnostic);
                    return output;
                }
            }
        }
    }

    // An equality a = b between BV terms lifts to f(a) = f(b) only through a
    // conversion f that both terms use; sbv_to_int(a) = ubv_to_int(b) does
    // not follow. Each conversion (view) therefore gets its own spanning
    // forest, or all pairs, over the class members that use it, and the zero
    // anchor joins every interpreted view.
    struct Injection
    {
        std::size_t lhs;
        std::size_t rhs;
        Z3_func_decl conversion;
        // lhs is read signed and rhs unsigned:
        // sbv(lhs) = ubv(rhs) - 2^n * msb(rhs).
        bool through_msb = false;
    };
    std::vector<Injection> injections;
    for (const auto &block : result.classes)
    {
        if (block.size() < 2)
            continue;
        std::optional<std::size_t> zero;
        std::vector<Z3_func_decl> views;
        for (const std::size_t index : block)
        {
            if (is_bv_zero_numeral(terms.at(index)))
            {
                zero = index;
                continue;
            }
            for (const Z3_func_decl conversion : term_infos.at(index).conversions)
                if (std::find(views.begin(), views.end(), conversion) == views.end())
                    views.push_back(conversion);
        }
        for (const Z3_func_decl view : views)
        {
            const bool with_zero =
                zero && is_semantic_bv_to_int_decl(context, view);
            std::vector<std::size_t> members;
            for (const std::size_t index : block)
            {
                const auto &conversions = term_infos.at(index).conversions;
                if (index == zero
                        ? with_zero
                        : std::find(conversions.begin(), conversions.end(),
                                    view) != conversions.end())
                    members.push_back(index);
            }
            if (prepass_options.inject_all_pairs)
            {
                for (std::size_t i = 0; i < members.size(); ++i)
                    for (std::size_t j = i + 1; j < members.size(); ++j)
                        injections.push_back({members[i], members[j], view});
            }
            else
            {
                // Equality transitivity derives every omitted pair, while
                // avoiding quadratic eqP assertions and native propagations.
                const std::size_t anchor = with_zero ? *zero : members.front();
                for (const std::size_t index : members)
                    if (index != anchor)
                        injections.push_back({anchor, index, view});
            }
        }
    }

    // A proof edge whose terms share no view, typically a cast from an
    // unsigned to a signed name, still relates the signed view of one term to
    // the unsigned view of the other through the top bit.
    // --eq-gb-partition-prepass-lift-casts states that relation per class:
    // each unsigned member against one signed member, through its own top
    // bit, which covers every cross-view pair whatever edges the forest has.
    auto view_of_kind = [&](const std::vector<Z3_func_decl> &views,
                            Z3_decl_kind kind) -> Z3_func_decl
    {
        for (const Z3_func_decl view : views)
            if (z3::func_decl(context, view).decl_kind() == kind)
                return view;
        return nullptr;
    };
    for (const auto &[lhs_index, rhs_index] : result.proof_edges)
    {
        // Every member of a zero class has an interpreted view (checked above).
        if (is_bv_zero_numeral(terms.at(lhs_index)) ||
            is_bv_zero_numeral(terms.at(rhs_index)))
            continue;
        const auto &lhs_views = term_infos.at(lhs_index).conversions;
        const auto &rhs_views = term_infos.at(rhs_index).conversions;
        if (std::any_of(lhs_views.begin(), lhs_views.end(),
                        [&](const Z3_func_decl view) {
                            return std::find(rhs_views.begin(), rhs_views.end(),
                                             view) != rhs_views.end();
                        }))
            continue;
        ++output.cross_view_edges;
    }
    if (prepass_options.lift_casts)
    {
        for (const auto &block : result.classes)
        {
            std::optional<std::size_t> signed_anchor;
            Z3_func_decl signed_view = nullptr;
            for (const std::size_t index : block)
            {
                if (is_bv_zero_numeral(terms.at(index)))
                    continue;
                signed_view = view_of_kind(term_infos.at(index).conversions,
                                           Z3_OP_SBV2INT);
                if (signed_view)
                {
                    signed_anchor = index;
                    break;
                }
            }
            if (!signed_anchor)
                continue;
            for (const std::size_t index : block)
            {
                if (index == *signed_anchor ||
                    is_bv_zero_numeral(terms.at(index)) ||
                    !view_of_kind(term_infos.at(index).conversions,
                                  Z3_OP_BV2INT))
                    continue;
                injections.push_back({*signed_anchor, index, signed_view, true});
                ++output.cross_view_lifted;
            }
        }
    }

    // An input with only eqmod atoms never applies eqP; declare it with the
    // prelude's signature, which yields the same declaration.
    std::optional<z3::func_decl> declared_eqp;
    if (!injections.empty() && injection_decls.pconst && !injection_decls.eqp)
    {
        const z3::sort poly =
            z3::func_decl(context, injection_decls.pconst).range();
        declared_eqp = context.function("eqP", poly, poly, context.bool_sort());
        injection_decls.eqp = static_cast<Z3_func_decl>(*declared_eqp);
    }

    if (!injections.empty() &&
        (!injection_decls.pconst || !injection_decls.eqp))
        throw std::runtime_error(
            "partition equality prepass proved equalities but cannot find "
            "PConst/eqP declarations in the input assertions");

    std::unordered_set<std::string> seen_assertions;
    for (const auto &block : result.classes)
    {
        if (block.size() < 2)
            continue;
        if (log)
        {
            std::ostringstream members;
            for (std::size_t i = 0; i < block.size(); ++i)
            {
                if (i != 0)
                    members << ", ";
                members << compact(terms.at(block[i]).to_string());
            }
            LOG_INFO(*log, "eqpartition",
                     "prepass complete equality class size=" +
                         std::to_string(block.size()) + " terms={" +
                         members.str() + "}");
        }
    }

    auto inject_terms = [&](const TermInfo &lhs, const TermInfo &rhs,
                            const Z3_func_decl selected_conversion,
                            bool through_msb)
    {
        if (is_bv_zero_numeral(rhs.term) &&
            !is_semantic_bv_to_int_decl(context, selected_conversion))
            throw std::runtime_error(
                "partition equality prepass cannot map zero through an "
                "uninterpreted conversion");
        z3::func_decl conversion(context, selected_conversion);
        if (conversion.arity() != 1 ||
            !z3::eq(conversion.domain(0), rhs.term.get_sort()))
            throw std::runtime_error(
                "partition equality prepass cannot share the selected "
                "BV-to-Int conversion across an equality pair");

        const z3::expr lhs_int = is_bv_zero_numeral(lhs.term)
                                     ? context.int_val(0)
                                     : conversion(lhs.term);
        const z3::expr rhs_int =
            is_bv_zero_numeral(rhs.term) ? context.int_val(0)
            : through_msb                ? signed_through_unsigned(rhs.term)
                                         : conversion(rhs.term);
        const z3::expr lhs_poly =
            apply_decl(context, injection_decls.pconst, {lhs_int});
        const z3::expr rhs_poly =
            apply_decl(context, injection_decls.pconst, {rhs_int});
        const z3::expr eqp =
            apply_decl(context, injection_decls.eqp, {lhs_poly, rhs_poly});
        const std::string key = eqp.to_string();
        if (!seen_assertions.insert(key).second)
            throw std::runtime_error(
                "partition equality prepass produced a duplicate eqP edge");

        output.assertions.push_back(eqp);
        output.equalities.emplace_back(lhs.term.to_string(),
                                       rhs.term.to_string());
        if (log)
            LOG_INFO(*log, "eqpartition",
                     "partition prepass injected equality: " +
                         compact(lhs.term.to_string()) + " == " +
                         compact(rhs.term.to_string()) + " as " +
                         compact(eqp.to_string()));
    };

    for (const Injection &injection : injections)
    {
        if (injection.lhs >= term_infos.size() ||
            injection.rhs >= term_infos.size())
            throw std::runtime_error(
                "partition equality prepass received an invalid equality pair");
        const TermInfo *lhs = &term_infos[injection.lhs];
        const TermInfo *rhs = &term_infos[injection.rhs];
        if (is_bv_zero_numeral(lhs->term) &&
            !is_bv_zero_numeral(rhs->term))
            std::swap(lhs, rhs);
        inject_terms(*lhs, *rhs, injection.conversion, injection.through_msb);
    }

    // A proved BV equality holds whatever view lifts it, so the native side
    // keeps one equality per proof edge (or implied pair), views aside.
    auto add_native = [&](std::size_t lhs_index, std::size_t rhs_index)
    {
        const z3::expr *lhs = &term_infos.at(lhs_index).term;
        const z3::expr *rhs = &term_infos.at(rhs_index).term;
        if (is_bv_zero_numeral(*lhs) && !is_bv_zero_numeral(*rhs))
            std::swap(lhs, rhs);
        output.native_equalities.emplace_back(*lhs, *rhs);
    };
    if (prepass_options.inject_all_pairs)
    {
        for (const auto &block : result.classes)
            for (std::size_t i = 0; i < block.size(); ++i)
                for (std::size_t j = i + 1; j < block.size(); ++j)
                    add_native(block[i], block[j]);
    }
    else
    {
        for (const auto &[lhs_index, rhs_index] : result.proof_edges)
            add_native(lhs_index, rhs_index);
    }

    output.injected_eqps = output.assertions.size();
    if (result.proof_edges.size() != result.statistics.proof_edges)
        throw std::runtime_error(
            "partition equality prepass proof-edge statistic is inconsistent");
    if (output.injected_eqps != injections.size())
        throw std::runtime_error(
            "partition equality prepass did not inject every planned equality");
    if (output.native_equalities.size() !=
        (prepass_options.inject_all_pairs ? result.statistics.implied_pairs
                                          : result.proof_edges.size()))
        throw std::runtime_error(
            "partition equality prepass did not retain every native proof edge");

    log_summary();
    return output;
}

} // namespace util::eqpartition
