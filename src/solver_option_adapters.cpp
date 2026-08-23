#include "solver_option_adapters.hpp"

namespace solver_options
{

std::optional<util::eqpartition::PrepassOptions>
make_partition_prepass_options(const cli::Options &options)
{
    if (options.eq_gb_partition_prepass_variant ==
            cli::EqGbPartitionPrepassVariant::Default &&
        !options.eq_gb_partition_prepass_workers &&
        !options.eq_gb_partition_prepass_all_pairs &&
        !options.eq_gb_partition_prepass_bv1_zero_anchor)
    {
        return std::nullopt;
    }

    util::eqpartition::PrepassOptions result;
    result.z3_only = options.eq_gb_partition_prepass_z3_only;
    switch (options.eq_gb_partition_prepass_scheduler)
    {
    case cli::EqGbPartitionPrepassScheduler::Auto:
        result.parallel_scheduler =
            util::eqpartition::ParallelScheduler::Auto;
        break;
    case cli::EqGbPartitionPrepassScheduler::Persistent:
        result.parallel_scheduler =
            util::eqpartition::ParallelScheduler::Persistent;
        break;
    case cli::EqGbPartitionPrepassScheduler::Portfolio:
        result.parallel_scheduler =
            util::eqpartition::ParallelScheduler::Portfolio;
        break;
    }

    result.inject_all_pairs = options.eq_gb_partition_prepass_all_pairs;
    // Unified production BPR always includes the unique BV1 zero anchor when
    // the conversion-backed BV1 universe is non-empty. The legacy flag is a
    // compatibility alias that still selects the configurable call path.
    result.include_bv1_zero_anchor = true;
    result.bv1_zero_timeout_ms =
        options.eq_gb_partition_prepass_bv1_zero_timeout_ms.value_or(0);
    result.bv1_zero_workers =
        options.eq_gb_partition_prepass_bv1_zero_workers;
    result.bv1_zero_exact_queries =
        options.eq_gb_partition_prepass_bv1_zero_only;
    result.bv1_zero_only = options.eq_gb_partition_prepass_bv1_zero_only;
    result.concurrent_widths =
        options.eq_gb_partition_prepass_concurrent_widths;

    if (options.eq_gb_partition_prepass_workers &&
        *options.eq_gb_partition_prepass_workers > 1)
    {
        result.experimental_variant = util::eqpartition::Variant::ParallelBpr;
        result.parallel_workers = *options.eq_gb_partition_prepass_workers;
    }

    switch (options.eq_gb_partition_prepass_bv1_zero_backend)
    {
    case cli::Bv1ZeroBackend::Z3:
        result.bv1_zero_backend = util::eqpartition::Bv1ZeroBackend::Z3;
        break;
    case cli::Bv1ZeroBackend::Boolector:
        result.bv1_zero_backend =
            util::eqpartition::Bv1ZeroBackend::Boolector;
        break;
    case cli::Bv1ZeroBackend::Bitwuzla:
        result.bv1_zero_backend =
            util::eqpartition::Bv1ZeroBackend::Bitwuzla;
        break;
    }

    switch (options.eq_gb_partition_prepass_variant)
    {
    case cli::EqGbPartitionPrepassVariant::Z3Mpm:
        result.experimental_variant = util::eqpartition::Variant::Z3Mpm;
        break;
    case cli::EqGbPartitionPrepassVariant::Hipr:
        result.experimental_variant = util::eqpartition::Variant::Hipr;
        break;
    case cli::EqGbPartitionPrepassVariant::Ipr:
        result.experimental_variant = util::eqpartition::Variant::Ipr;
        break;
    case cli::EqGbPartitionPrepassVariant::Abipr:
        result.experimental_variant = util::eqpartition::Variant::Abipr;
        break;
    case cli::EqGbPartitionPrepassVariant::Sopr:
        result.experimental_variant = util::eqpartition::Variant::Sopr;
        break;
    case cli::EqGbPartitionPrepassVariant::Hsopr:
        result.experimental_variant = util::eqpartition::Variant::Hsopr;
        break;
    case cli::EqGbPartitionPrepassVariant::Bitwuzla:
        result.experimental_variant = util::eqpartition::Variant::Bitwuzla;
        result.parallel_workers =
            options.eq_gb_partition_prepass_parallel_workers.value_or(1);
        result.parallel_query_timeout_ms =
            options.eq_gb_partition_prepass_parallel_query_timeout_ms.value_or(0);
        break;
    case cli::EqGbPartitionPrepassVariant::Boolector:
        result.experimental_variant = util::eqpartition::Variant::Boolector;
        result.parallel_workers =
            options.eq_gb_partition_prepass_parallel_workers.value_or(1);
        result.parallel_query_timeout_ms =
            options.eq_gb_partition_prepass_parallel_query_timeout_ms.value_or(0);
        break;
    case cli::EqGbPartitionPrepassVariant::ParallelBpr:
        result.experimental_variant = util::eqpartition::Variant::ParallelBpr;
        result.parallel_workers =
            options.eq_gb_partition_prepass_parallel_workers.value_or(4);
        result.parallel_query_timeout_ms =
            options.eq_gb_partition_prepass_parallel_query_timeout_ms.value_or(0);
        result.parallel_boolector_global_fallback =
            options.eq_gb_partition_prepass_parallel_boolector_fallback;
        if (options.eq_gb_partition_prepass_parallel_boolector_embedded_global_fallback)
            result.parallel_embedded_global_fallback =
                util::eqpartition::ParallelFallbackBackend::Boolector;
        else if (options.eq_gb_partition_prepass_parallel_bitwuzla_embedded_global_fallback)
            result.parallel_embedded_global_fallback =
                util::eqpartition::ParallelFallbackBackend::Bitwuzla;
        if (options.eq_gb_partition_prepass_parallel_boolector_direct_fallback)
            result.parallel_fallback =
                util::eqpartition::ParallelFallbackBackend::Boolector;
        else if (options.eq_gb_partition_prepass_parallel_bitwuzla_direct_fallback)
            result.parallel_fallback =
                util::eqpartition::ParallelFallbackBackend::Bitwuzla;
        result.parallel_final_global_validation =
            options.eq_gb_partition_prepass_parallel_final_validation;
        break;
    case cli::EqGbPartitionPrepassVariant::Default:
        break;
    }

    return result;
}

} // namespace solver_options
