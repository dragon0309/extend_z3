#pragma once

#include <z3++.h>

#include <cstddef>
#include <chrono>
#include <string>
#include <vector>

#include "util/logger.hpp"

namespace util::autozero
{

struct Result
{
    std::vector<std::string> implied_zero_bases;
    // Coefficient terms that can be mapped back to an injected eqP.
    std::size_t coefficient_target_count = 0;
    // Terms submitted to the zero-anchor validator: every symbolic BV1
    // constant in projected F plus all coefficient targets.
    std::size_t validation_candidate_count = 0;
};

enum class DiscoveryMode
{
    GroupedZeroAnchor,
    Callback
};

struct SingletonZeroValidationResult
{
    std::vector<z3::expr> proved_terms;
    std::size_t candidates = 0;
    std::size_t checks = 0;
    std::size_t refuted = 0;
    std::size_t unknown = 0;
    std::size_t model_pruned = 0;
    bool constraints_unsat = false;
    std::chrono::nanoseconds elapsed{0};
};

// Validate BV1 candidates independently against zero. Each solver batch
// contains at most one disequality candidate. Only UNSAT results are returned
// as proved; SAT and unknown candidates are omitted. exact_queries disables
// seed/model sharing so every F AND candidate != #b0 query is actually run.
SingletonZeroValidationResult validate_bv1_singleton_zeros(
    z3::context &ctx,
    const std::vector<z3::expr> &projected_constraints,
    const std::vector<z3::expr> &candidates,
    util::Logger *log = nullptr,
    unsigned timeout_ms = 30000,
    std::size_t workers = 4,
    bool exact_queries = false);

// Prove ring-mapped BV terms equal to zero using the same positive-AND,
// Poly-free constraint projection as the equality partition prepass. Grouped
// zero-anchor BPR is the primary mode; callback mode only filters candidates
// and uses the same UNSAT-only validator. Returned strings are canonical Z3
// renderings of BV-to-Int coefficient bases.
Result discover_implied_zeros(z3::context &ctx,
                              const std::vector<z3::expr> &assertions,
                              DiscoveryMode mode,
                              util::Logger &log);

// Encode every globally proved coefficient-base zero as a top-level
// eqP(PConst(base), PConst(0)) assertion. This mirrors the equality partition
// prepass injection path so normal Rewrite and eqP compilation own the
// resulting polynomial relation.
std::vector<z3::expr> inject_as_eqp(
    z3::context &ctx,
    const std::vector<z3::expr> &assertions,
    const Result &result,
    util::Logger &log);

} // namespace util::autozero
