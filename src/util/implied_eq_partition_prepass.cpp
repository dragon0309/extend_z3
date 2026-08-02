#include "util/implied_eq_partition_prepass.hpp"

#include <algorithm>
#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>

#include "util/fmt_duration.hpp"
#include "util/logger.hpp"

namespace util::eqpartition
{
namespace
{

bool is_bv_to_int_app(const z3::expr &expression)
{
    if (!expression.is_app() || !expression.get_sort().is_int() ||
        expression.num_args() != 1 ||
        !expression.arg(0).get_sort().is_bv())
        return false;
#ifdef Z3_OP_BV2INT
    if (expression.decl().decl_kind() == Z3_OP_BV2INT)
        return true;
#endif
    const std::string name = expression.decl().name().str();
    return name == "ubv_to_int" || name == "sbv_to_int" ||
           name == "bv2nat" || name == "bv2int";
}

bool assertion_contains_poly(const z3::expr &expression)
{
    if (!expression.is_app())
        return false;
    const std::string name = expression.decl().name().str();
    if (name == "eqP" || name == "eqmodP1" || name == "eqmodP2" ||
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
        if (!term.is_const() || term.is_numeral())
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
    std::vector<z3::expr> terms;
    terms.reserve(term_infos.size());
    for (const TermInfo &info : term_infos)
        terms.push_back(info.term);
    output.terms = terms.size();

    if (log)
        LOG_INFO(*log, "eqpartition",
                 "partition prepass started: constraints=" +
                     std::to_string(constraints.size()) +
                     " terms=" + std::to_string(terms.size()));

    Result selected_result;
    if (prepass_options.experimental_variant)
    {
        VariantOptions variant_options;
        variant_options.parallel_workers =
            prepass_options.parallel_workers;
        variant_options.parallel_final_global_validation =
            prepass_options.parallel_final_global_validation;
        selected_result = run_variant(
            context, constraints, terms,
            *prepass_options.experimental_variant, variant_options, log);
    }
    else
    {
        Options options;
        options.timeout_ms = 0;
        options.start_async = false;
        ImpliedEqualityPartitionRefiner refiner(
            context, constraints, terms, options, log);
        selected_result = refiner.wait();
    }
    const Result &result = selected_result;
    if (result.status != Status::Complete)
        throw std::runtime_error(
            "partition equality prepass did not complete: " +
            std::string(status_name(result.status)) +
            (result.diagnostic.empty()
                 ? std::string()
                 : std::string(" (") + result.diagnostic + ")"));
    output.partition_statistics = result.statistics;
    output.constraints_unsat = result.constraints_unsat;

    auto log_summary = [&]() {
        if (!log)
            return;
        const Statistics &stats = output.partition_statistics;
        LOG_INFO(*log, "eqpartition",
                 "partition prepass summary: status=complete constraints=" +
                     std::to_string(output.constraints) +
                     " terms=" + std::to_string(output.terms) +
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
                     " final-validation-checks=" +
                     std::to_string(stats.final_validation_checks) +
                     " final-validation-time=" +
                     util::fmt_duration(stats.final_validation_time) +
                     " equality-classes=" +
                     std::to_string(stats.equality_classes) +
                     " proof-edges=" +
                     std::to_string(stats.proof_edges) +
                     " implied-pairs=" +
                     std::to_string(stats.implied_pairs) +
                     " injected-eqps=" +
                     std::to_string(output.injected_eqps) +
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

    if (result.statistics.implied_pairs != 0 &&
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

    auto inject_pair = [&](std::size_t lhs_index, std::size_t rhs_index)
    {
        if (lhs_index >= term_infos.size() || rhs_index >= term_infos.size())
            throw std::runtime_error(
                "partition equality prepass received an invalid equality pair");
        const TermInfo &lhs = term_infos[lhs_index];
        const TermInfo &rhs = term_infos[rhs_index];
        if (lhs.conversions.empty())
            throw std::runtime_error(
                "partition equality prepass term has no BV-to-Int conversion");

        z3::func_decl conversion(context, lhs.conversions.front());
        if (conversion.arity() != 1 ||
            !z3::eq(conversion.domain(0), rhs.term.get_sort()))
            throw std::runtime_error(
                "partition equality prepass cannot share the selected "
                "BV-to-Int conversion across an equality pair");

        const z3::expr lhs_int = conversion(lhs.term);
        const z3::expr rhs_int = conversion(rhs.term);
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
        output.native_equalities.emplace_back(lhs.term, rhs.term);
        if (log)
            LOG_INFO(*log, "eqpartition",
                     "partition prepass injected equality: " +
                         compact(lhs.term.to_string()) + " == " +
                         compact(rhs.term.to_string()) + " as " +
                         compact(eqp.to_string()));
    };

    for (const auto &block : result.classes)
    {
        for (std::size_t i = 0; i < block.size(); ++i)
            for (std::size_t j = i + 1; j < block.size(); ++j)
                inject_pair(block[i], block[j]);
    }

    output.injected_eqps = output.assertions.size();
    if (output.injected_eqps != result.statistics.implied_pairs)
        throw std::runtime_error(
            "partition equality prepass did not inject every implied pair");
    if (output.native_equalities.size() != output.injected_eqps)
        throw std::runtime_error(
            "partition equality prepass did not retain every native equality pair");

    log_summary();
    return output;
}

} // namespace util::eqpartition
