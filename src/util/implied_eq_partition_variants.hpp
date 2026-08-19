#pragma once

#include <z3++.h>

#include <chrono>
#include <cstddef>
#include <vector>

#include "util/implied_eq_partition_refiner.hpp"

namespace util
{
class Logger;
}

namespace util::eqpartition
{

enum class Variant
{
    Z3Mpm,
    Hipr,
    Ipr,
    Abipr,
    Sopr,
    Hsopr,
    Bitwuzla,
    Boolector,
    ParallelBpr
};

const char *variant_name(Variant variant);

enum class ParallelFallbackBackend
{
    None,
    Boolector,
    Bitwuzla
};

enum class ParallelScheduler
{
    Auto,
    Persistent,
    Portfolio
};

const char *parallel_fallback_name(ParallelFallbackBackend backend);

enum class NativeSingletonBackend
{
    Boolector,
    Bitwuzla
};

enum class NativeSingletonOutcome
{
    Sat,
    Unsat,
    Unknown
};

struct NativeSingletonValidationResult
{
    std::vector<NativeSingletonOutcome> outcomes;
    std::size_t checks = 0;
    std::size_t sat = 0;
    std::size_t unsat = 0;
    std::size_t unknown = 0;
    std::chrono::nanoseconds elapsed{0};
};

// Run exactly one F AND candidate != #b0 query per BV1 candidate. Each bounded
// batch owns independent fresh native solver instances. SAT models are not
// used to prune other candidates.
NativeSingletonValidationResult run_native_bv1_singleton_queries(
    z3::context &source_context,
    const std::vector<z3::expr> &source_constraints,
    const std::vector<z3::expr> &source_candidates,
    NativeSingletonBackend backend,
    std::size_t workers,
    unsigned timeout_ms,
    util::Logger *log = nullptr);

struct VariantOptions
{
    std::size_t parallel_workers = 4;
    bool z3_only = false;
    ParallelScheduler parallel_scheduler = ParallelScheduler::Auto;
    // Zero restores unbounded worker queries. A non-zero timeout bounds each
    // synchronous epoch; timed-out edges remain unresolved and are retried.
    unsigned parallel_query_timeout_ms = 0;
    bool parallel_boolector_global_fallback = false;
    // Embedded global fallback solves one query over every active edge.
    // Native SAT supplies free inputs for a Z3 F+inputs completion; native
    // UNSAT certifies every active representative edge.
    ParallelFallbackBackend parallel_embedded_global_fallback =
        ParallelFallbackBackend::None;
    ParallelFallbackBackend parallel_fallback =
        ParallelFallbackBackend::None;
    bool parallel_final_global_validation = false;
};

// Experimental alternatives used only when explicitly selected by the
// partition-prepass CLI. The existing ImpliedEqualityPartitionRefiner remains
// the default implementation and does not call this function.
Result run_variant(
    z3::context &source_context,
    const std::vector<z3::expr> &source_constraints,
    const std::vector<z3::expr> &source_terms,
    Variant variant,
    util::Logger *log = nullptr);

Result run_variant(
    z3::context &source_context,
    const std::vector<z3::expr> &source_constraints,
    const std::vector<z3::expr> &source_terms,
    Variant variant,
    const VariantOptions &options,
    util::Logger *log = nullptr);

} // namespace util::eqpartition
