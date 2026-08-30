#pragma once

#include <z3++.h>

#include <chrono>
#include <cstddef>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "util/implied_eq_partition_refiner.hpp"
#include "util/implied_eq_partition_variants.hpp"

namespace util
{
class Logger;
}

namespace util::eqpartition
{

enum class Bv1ZeroBackend
{
    Z3,
    Boolector
};

struct PrepassResult
{
    Status status = Status::Error;
    std::string diagnostic;
    std::size_t constraints = 0;
    std::size_t original_terms = 0;
    std::size_t anchor_terms = 0;
    std::size_t terms = 0;
    std::size_t injected_eqps = 0;
    bool bv1_zero_anchor_added = false;
    std::size_t bv1_zero_candidates = 0;
    std::size_t bv1_zero_proved = 0;
    std::size_t bv1_zero_refuted = 0;
    std::size_t bv1_zero_unknown = 0;
    std::size_t bv1_zero_checks = 0;
    std::chrono::nanoseconds bv1_zero_elapsed{0};
    // True when the initial plain non-Poly constraint check returned UNSAT.
    // In this case prepass intentionally injects nothing and lets the normal
    // main pipeline solve the original assertions.
    bool constraints_unsat = false;
    std::size_t final_classes = 0;
    std::size_t bv1_zero_count = 0;
    std::string class_digest;
    std::string zero_digest;
    std::vector<std::vector<std::string>> canonical_classes;
    std::vector<std::string> canonical_zero_terms;
    Statistics partition_statistics;
    std::vector<std::pair<std::string, std::string>> equalities;
    // Native BV injection edges corresponding one-for-one with
    // equalities/assertions. They are retained so the main user propagator can
    // optionally replay the selected forest or all-pairs representation after
    // Z3 search has entered a legal callback.
    std::vector<std::pair<z3::expr, z3::expr>> native_equalities;
    std::vector<z3::expr> assertions;
};

struct PrepassOptions
{
    // Empty preserves the existing fresh-solver BPR implementation exactly.
    std::optional<Variant> experimental_variant;
    std::size_t parallel_workers = 4;
    // Benchmark/control mode for Unified BPR: keep the same scheduler and
    // worker count, but disable every automatic native-solver accelerator.
    bool z3_only = false;
    ParallelScheduler parallel_scheduler = ParallelScheduler::Auto;
    unsigned parallel_query_timeout_ms = 0;
    bool parallel_boolector_global_fallback = false;
    ParallelFallbackBackend parallel_embedded_global_fallback =
        ParallelFallbackBackend::None;
    ParallelFallbackBackend parallel_fallback =
        ParallelFallbackBackend::None;
    bool parallel_final_global_validation = false;
    // Compatibility mode: materialize every C(k,2) pair instead of the
    // default k-1 proof-edge spanning forest for each size-k class.
    bool inject_all_pairs = false;
    // Unified production mode adds #b0 directly to the full BV1 partition.
    // The backend/worker fields below are retained only for the legacy
    // zero-only benchmark path.
    bool include_bv1_zero_anchor = true;
    Bv1ZeroBackend bv1_zero_backend = Bv1ZeroBackend::Z3;
    std::size_t bv1_zero_workers = 4;
    // Execute every singleton query without seed/model pruning. This is
    // enabled by the zero-only benchmark mode for apples-to-apples results.
    bool bv1_zero_exact_queries = false;
    // Stop after BV1 validation. No non-BV1 partition or eqP injection runs.
    bool bv1_zero_only = false;
    // Run BV1 validation and the selected non-BV1 backend concurrently. The
    // default refiner already supports this; experimental variants first copy
    // their source problem to an isolated context before launching a thread.
    bool concurrent_widths = false;
    // Legacy zero-only benchmark timeout. Production unified BPR never uses
    // a correctness timeout.
    unsigned bv1_zero_timeout_ms = 0;
};

// Runs complete implied-equality partition refinement before the main Z3
// solver is constructed. The conversion-backed BV1 universe automatically
// includes one #b0 anchor. If the non-Poly constraints are satisfiable,
// encodes a spanning forest (k-1 edges for a size-k class) as eqP assertions
// by default. Classes containing #b0 use it as the forest anchor.
// Equality transitivity represents omitted pairs. If the constraints are UNSAT,
// returns no assertions so the normal main pipeline solves the original
// formula. Every returned equality is global with respect to the selected
// non-Poly BV constraint subset.
PrepassResult run_eqp_prepass(
    z3::context &context,
    const std::vector<z3::expr> &source_assertions,
    util::Logger *log = nullptr);

PrepassResult run_eqp_prepass(
    z3::context &context,
    const std::vector<z3::expr> &source_assertions,
    const PrepassOptions &options,
    util::Logger *log = nullptr);

} // namespace util::eqpartition
