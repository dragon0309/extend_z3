#pragma once

#include <cstddef>
#include <iosfwd>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "util/eq_callback.hpp"

namespace cli
{

enum class EqGbPartitionPrepassVariant
{
    Default,
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

enum class Bv1ZeroBackend
{
    Z3,
    Boolector,
    Bitwuzla
};

enum class EqGbPartitionPrepassScheduler
{
    Auto,
    Persistent,
    Portfolio
};

struct Options
{
    std::string input_file;
    std::string option_summary = "(none)";

    bool ring_detail = false;
    bool no_trace = false;
    bool enable_all_false = true;
    bool enable_all_true = true;
    bool enable_mixed = true;
    // User promise: each same-modulus P1 group handled by the product
    // refutation generates a prime ideal in the concrete polynomial ring.
    bool all_false_assume_m_prime = false;
    bool enable_rewriting = true;
    bool preserve_eqmodp1_vars = false;
    bool enable_subexpression_rules = false;
    bool enable_raw_poly_power_rules = false;
    bool enable_expression_growth_check = false;
    bool enable_rewrite_singular_nf = true;
    bool enable_moduli_normalization = false;
    bool disable_rewrite_cache = false;
    bool verify_rewrite_lookups = false;
    bool enable_auto_zero_lemmas_bv1_callback = false;
    bool enable_auto_zero_lemmas = false;
    bool enable_final_fixed_value_check = true;
    bool enable_eqmod_true_lemmas = false;
    bool enable_eqmod_true_lemma_lift_antecedents = false;
    bool enable_gb_preprocess = false;
    bool verify_gb_preprocess = false;
    bool enable_ideal_rewrite = false;
    std::size_t eq_gb_true_lemma_processes = 0;
    bool eq_gb_reuse_base_basis = false;
    std::size_t eq_gb_refutation_processes = 0;
    bool enable_minimal_fixed_watch = false;
    bool enable_eq_gb_live = false;
    bool eq_gb_live_hybrid = false;
    bool eq_gb_live_partition_refinement = false;
    bool eq_gb_partition_prepass_propagation = false;
    bool eq_gb_live_propagate = true;
    bool eq_gb_live_generators = true;
    bool eq_gb_live_seed_models = true;
    bool eq_gb_live_unified_queue = false;
    std::size_t eq_gb_live_workers = 4;
    bool enable_eq_gb_partition_prepass = false;
    std::optional<std::size_t> eq_gb_partition_prepass_workers;
    bool eq_gb_partition_prepass_z3_only = false;
    EqGbPartitionPrepassScheduler eq_gb_partition_prepass_scheduler =
        EqGbPartitionPrepassScheduler::Auto;
    bool eq_gb_partition_prepass_scheduler_explicit = false;
    bool eq_gb_partition_prepass_all_pairs = false;
    bool eq_gb_partition_prepass_bv1_zero_anchor = false;
    std::optional<unsigned> eq_gb_partition_prepass_bv1_zero_timeout_ms;
    std::size_t eq_gb_partition_prepass_bv1_zero_workers = 4;
    Bv1ZeroBackend eq_gb_partition_prepass_bv1_zero_backend =
        Bv1ZeroBackend::Z3;
    bool eq_gb_partition_prepass_bv1_zero_workers_explicit = false;
    bool eq_gb_partition_prepass_bv1_zero_backend_explicit = false;
    bool eq_gb_partition_prepass_bv1_zero_only = false;
    bool eq_gb_partition_prepass_concurrent_widths = false;
    EqGbPartitionPrepassVariant eq_gb_partition_prepass_variant =
        EqGbPartitionPrepassVariant::Default;
    std::optional<std::size_t> eq_gb_partition_prepass_parallel_workers;
    std::optional<unsigned> eq_gb_partition_prepass_parallel_query_timeout_ms;
    bool eq_gb_partition_prepass_parallel_boolector_fallback = false;
    bool eq_gb_partition_prepass_parallel_boolector_embedded_global_fallback = false;
    bool eq_gb_partition_prepass_parallel_bitwuzla_embedded_global_fallback = false;
    bool eq_gb_partition_prepass_parallel_boolector_direct_fallback = false;
    bool eq_gb_partition_prepass_parallel_bitwuzla_direct_fallback = false;
    bool eq_gb_partition_prepass_parallel_final_validation = false;
    bool enable_eq_gb_z3 = false;
    bool enable_eq_gb_z3_parallel_candidates = false;
    bool enable_bv_eq_fallback = false;
    bool enable_eq_gb_z3_all_bv_constants = false;
    std::size_t eq_gb_z3_validation_batch_size = 64;
    std::size_t eq_gb_z3_seeded_candidate_solvers = 4;
    std::vector<std::pair<std::string, std::string>> inject_ideal_eq;
    bool log_conflict_ants = false;
    bool use_groebner_ring_var_order = true;
    bool dump_singular = false;
    bool show_model_on_terminal = false;
    bool rewrite_log_requested = false;
    bool print_fixed_all = true;
    util::EqCallbackOptions eq_callback_options;
};

struct ParseResult
{
    Options options;
    bool ok = false;
    bool selftest = false;
    bool missing_input = false;
    bool show_usage = false;
    bool log_error = false;
    std::string error;
};

ParseResult parse_options(int argc, char **argv);
void print_usage(std::ostream &os, const char *program);

} // namespace cli
