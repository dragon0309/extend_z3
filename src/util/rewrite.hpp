#pragma once

#include <z3++.h>
#include <Singular/libsingular.h>

#include <gmpxx.h>
#include <cstddef>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

class Logger;

struct RewriteOptions
{
    bool enable_rewriting = true;
    bool use_singular_normalization = true;
    bool use_subexpression_rules = true;
    bool conservative_mode = true;
    std::size_t max_rounds = 100;
    std::size_t max_expression_growth = 4096;

    // Compatibility knobs accepted by main.cpp. The old heuristic pipeline is
    // gone; these are mapped onto the OCaml-style extractor where meaningful.
    bool enable_expr_rewriting = true;
    bool suppress_expr_rhs_for_eqmodp1_atoms = true;

    std::unordered_set<std::string> suppressed_lhs_keys;
};

using RewriteConfig = RewriteOptions;

struct RewriteRule
{
    enum class Kind
    {
        Variable,
        SubExpression
    };

    z3::expr lhs;
    z3::expr rhs;
    z3::expr source_generator;
    std::vector<std::string> rhs_dependencies;
    Kind kind = Kind::Variable;
    bool is_modular = false;
    std::string source_label;

    RewriteRule(const z3::expr &lhs_,
                const z3::expr &rhs_,
                const z3::expr &source_,
                Kind kind_,
                bool modular_,
                std::string label_ = {});
};

// Legacy log representation retained for main.cpp diagnostics.
struct PolyRewriteRule
{
    enum class Kind
    {
        Alias,
        ToZero,
        ToConst,
        ExprRhs
    };

    bool to_zero = false;
    bool to_const = false;
    mpz_class const_value = 0;
    std::string target;
    Kind kind = Kind::Alias;

    std::optional<z3::expr> rhs_int;
    std::unordered_set<std::string> rhs_atoms;
    std::string source_label;

    bool is_modular = false;
    mpz_class modulus = 0;
};

struct RewriteStats
{
    std::size_t rules_extracted = 0;
    std::size_t duplicate_lhs = 0;
    std::size_t conflicting_lhs = 0;
    std::size_t skipped_nonlinear = 0;
    std::size_t skipped_unsafe_coefficient = 0;
    std::size_t skipped_lhs_occurs_in_rhs = 0;
    std::size_t skipped_modulus_not_subsumed = 0;
    std::size_t skipped_expression_growth = 0;
    std::size_t singular_nf_checks = 0;
    std::size_t singular_zero_reductions = 0;
    std::size_t singular_failures = 0;
};

struct RewriteResult
{
    std::vector<z3::expr> residual_generators;
    z3::expr rewritten_target;
    std::vector<RewriteRule> rules_used;
    bool used_worklist_fallback = false;
    std::size_t dag_rounds = 0;
    RewriteStats stats;
    std::vector<std::string> diagnostics;

    // Assertion-level wrapper output used by main.cpp.
    std::vector<z3::expr> asserts;
    int generators_before = 0;
    int unique_vars_before = 0;
    int generators_after = 0;
    int unique_vars_after = 0;
    std::unordered_map<std::string, PolyRewriteRule> rewrite_rules;
    std::size_t legacy_rule_count = 0;
    std::size_t expr_rule_count = 0;
    std::vector<std::string> rewrite_skipped_log;
    std::vector<std::string> rewrite_dropped_cycles;

    explicit RewriteResult(const z3::expr &target);
};

struct AnnotatedPolynomial
{
    z3::expr polynomial;
    std::string annotation;

    AnnotatedPolynomial(const z3::expr &poly, std::string annot = {});
};

struct AnnotatedPostcondition
{
    z3::expr postcondition;
    z3::expr polynomial;
    std::vector<z3::expr> moduli;
    std::string annotation;

    AnnotatedPostcondition(const z3::expr &post,
                           const z3::expr &poly,
                           std::vector<z3::expr> ms = {},
                           std::string annot = {});
};

struct RewriteTwoPhaseResult
{
    std::vector<AnnotatedPolynomial> ideal_polynomials;
    std::vector<AnnotatedPostcondition> postconditions;
    std::vector<RewriteRule> rules_used;
    RewriteStats stats;
    std::vector<std::string> diagnostics;
};

RewriteResult rewrite_assignments(
    const std::vector<z3::expr> &ideal_generators,
    const z3::expr &target,
    const std::vector<z3::expr> &moduli = {},
    RewriteOptions options = {});

RewriteTwoPhaseResult rewrite_assignments_two_phase(
    const std::vector<AnnotatedPolynomial> &ideal_polynomials,
    const std::vector<AnnotatedPostcondition> &postconditions,
    const std::vector<z3::expr> &moduli = {},
    RewriteOptions options = {});

RewriteResult run_rewriting_pipeline(
    z3::context &ctx,
    const std::vector<z3::expr> &input_asserts,
    const RewriteConfig &config,
    Logger &log);

std::string rule_rhs_pretty(const PolyRewriteRule &rr);

std::string pretty_rewrite_atom_name(const std::string &s);

int run_rewrite_selftests();

/** Shared ℤ coeffs for libsingular — one global domain; callers must borrow with
 *  nCopyCoeff(...) before passing the pointer to rDefault (pair with rDelete). */
coeffs singular_shared_coeffs_Z();
