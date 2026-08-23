#include "cli_options.hpp"

#include <algorithm>
#include <cctype>
#include <limits>
#include <ostream>
#include <sstream>
#include <stdexcept>
#include <utility>

namespace cli
{
namespace
{

std::string join_options(int argc, char **argv)
{
    if (argc <= 2)
        return "(none)";

    std::ostringstream oss;
    for (int i = 2; i < argc; ++i)
    {
        if (i > 2)
            oss << ' ';
        oss << argv[i];
    }
    return oss.str();
}

bool is_unsigned_integer(const std::string &value)
{
    return !value.empty() &&
           std::all_of(value.begin(), value.end(),
                       [](unsigned char ch) { return std::isdigit(ch) != 0; });
}

bool parse_size(const std::string &value, std::size_t &out)
{
    try
    {
        out = std::stoull(value);
        return true;
    }
    catch (const std::exception &)
    {
        return false;
    }
}

bool parse_positive_process_count(int &index, int argc, char **argv,
                                  const std::string &option,
                                  std::size_t &out,
                                  std::string &error)
{
    if (index + 1 >= argc)
    {
        error = option + " requires one positive integer argument";
        return false;
    }
    const std::string value = argv[++index];
    if (!is_unsigned_integer(value) || !parse_size(value, out) ||
        out == 0 || out > 64)
    {
        error = option + " must be between 1 and 64";
        return false;
    }
    return true;
}

ParseResult error_result(Options options, std::string error,
                         bool show_usage = false, bool log_error = false)
{
    ParseResult result;
    result.options = std::move(options);
    result.error = std::move(error);
    result.show_usage = show_usage;
    result.log_error = log_error;
    return result;
}

} // namespace

ParseResult parse_options(int argc, char **argv)
{
    for (int i = 1; i < argc; ++i)
    {
        if (std::string(argv[i]) == "--selftest")
        {
            ParseResult result;
            result.ok = true;
            result.selftest = true;
            return result;
        }
    }

    Options options;
    if (argc < 2)
    {
        ParseResult result = error_result(std::move(options), "missing input file", true, true);
        result.missing_input = true;
        return result;
    }

    options.input_file = argv[1];
    options.option_summary = join_options(argc, argv);

    for (int i = 2; i < argc; ++i)
    {
        const std::string arg = argv[i];
        if (arg == "--ring-detail")
            options.ring_detail = true;
        else if (arg == "--no-trace")
            options.no_trace = true;
        else if (arg == "--disable-all-false")
            options.enable_all_false = false;
        else if (arg == "--disable-all-true")
            options.enable_all_true = false;
        else if (arg == "--disable-mixed")
            options.enable_mixed = false;
        else if (arg == "--m-prime")
            options.all_false_assume_m_prime = true;
        else if (arg == "--no-rewriting")
            options.enable_rewriting = false;
        else if (arg == "--no-singular-nf")
            options.enable_rewrite_singular_nf = false;
        else if (arg == "--enable-moduli-normalization")
            options.enable_moduli_normalization = true;
        else if (arg == "--preserve-eqmodp1-vars")
            options.preserve_eqmodp1_vars = true;
        else if (arg == "--enable-subexpression-rules")
            options.enable_subexpression_rules = true;
        else if (arg == "--enable-raw-poly-power-rules")
            options.enable_raw_poly_power_rules = true;
        else if (arg == "--enable-expression-growth-check")
            options.enable_expression_growth_check = true;
        else if (arg == "--disable-rewrite-cache")
            options.disable_rewrite_cache = true;
        else if (arg == "--verify-rewrite-lookups")
            options.verify_rewrite_lookups = true;
        else if (arg == "--auto-zero-lemmas-bv1-callback")
            options.enable_auto_zero_lemmas_bv1_callback = true;
        else if (arg == "--auto-zero-lemmas")
            options.enable_auto_zero_lemmas = true;
        else if (arg == "--disable-final-fixed-value-check")
            options.enable_final_fixed_value_check = false;
        else if (arg == "--minimal-fixed-watch")
            options.enable_minimal_fixed_watch = true;
        else if (arg == "--enable-eq-gb-live")
            options.enable_eq_gb_live = true;
        else if (arg == "--eq-gb-live-hybrid")
            options.eq_gb_live_hybrid = true;
        else if (arg == "--eq-gb-live-partition-refinement")
            options.eq_gb_live_partition_refinement = true;
        else if (arg == "--eq-gb-partition-prepass-propagation")
            options.eq_gb_partition_prepass_propagation = true;
        else if (arg == "--eq-gb-live-unified-queue")
            options.eq_gb_live_unified_queue = true;
        else if (arg == "--eq-gb-live-no-propagation")
            options.eq_gb_live_propagate = false;
        else if (arg == "--eq-gb-live-no-generators")
            options.eq_gb_live_generators = false;
        else if (arg == "--eq-gb-live-no-seed-models")
            options.eq_gb_live_seed_models = false;
        else if (arg == "--eq-gb-live-workers")
        {
            if (i + 1 >= argc)
                return error_result(std::move(options),
                                    "--eq-gb-live-workers requires one positive integer argument");
            const std::string value = argv[++i];
            if (!is_unsigned_integer(value))
                return error_result(std::move(options),
                                    "--eq-gb-live-workers requires one positive integer argument");
            if (!parse_size(value, options.eq_gb_live_workers))
                return error_result(std::move(options), "--eq-gb-live-workers is too large");
            if (options.eq_gb_live_workers == 0 ||
                options.eq_gb_live_workers > static_cast<std::size_t>(std::numeric_limits<unsigned>::max()))
            {
                return error_result(
                    std::move(options),
                    "--eq-gb-live-workers must be between 1 and " +
                        std::to_string(std::numeric_limits<unsigned>::max()));
            }
        }
        else if (arg == "--enable-eq-gb-z3")
            options.enable_eq_gb_z3 = true;
        else if (arg == "--enable-eq-gb-partition-prepass")
            options.enable_eq_gb_partition_prepass = true;
        else if (arg == "--eq-gb-partition-prepass-workers")
        {
            std::size_t workers = 0;
            std::string error;
            if (!parse_positive_process_count(
                    i, argc, argv, arg, workers, error))
                return error_result(std::move(options), std::move(error));
            options.eq_gb_partition_prepass_workers = workers;
        }
        else if (arg == "--eq-gb-partition-prepass-z3-only")
            options.eq_gb_partition_prepass_z3_only = true;
        else if (arg == "--eq-gb-partition-prepass-scheduler")
        {
            if (i + 1 >= argc)
                return error_result(
                    std::move(options),
                    "--eq-gb-partition-prepass-scheduler requires "
                    "auto, persistent, or portfolio");
            const std::string value = argv[++i];
            if (value == "auto")
                options.eq_gb_partition_prepass_scheduler =
                    EqGbPartitionPrepassScheduler::Auto;
            else if (value == "persistent")
                options.eq_gb_partition_prepass_scheduler =
                    EqGbPartitionPrepassScheduler::Persistent;
            else if (value == "portfolio")
                options.eq_gb_partition_prepass_scheduler =
                    EqGbPartitionPrepassScheduler::Portfolio;
            else
                return error_result(
                    std::move(options),
                    "--eq-gb-partition-prepass-scheduler must be "
                    "auto, persistent, or portfolio");
            options.eq_gb_partition_prepass_scheduler_explicit = true;
        }
        else if (arg == "--eq-gb-partition-prepass-all-pairs")
            options.eq_gb_partition_prepass_all_pairs = true;
        else if (arg == "--eq-gb-partition-prepass-bv1-zero-anchor")
            options.eq_gb_partition_prepass_bv1_zero_anchor = true;
        else if (arg ==
                 "--eq-gb-partition-prepass-bv1-zero-timeout-ms")
        {
            if (i + 1 >= argc)
                return error_result(
                    std::move(options),
                    "--eq-gb-partition-prepass-bv1-zero-timeout-ms "
                    "requires one non-negative integer argument");
            const std::string value = argv[++i];
            std::size_t parsed = 0;
            if (!is_unsigned_integer(value) || !parse_size(value, parsed) ||
                parsed > static_cast<std::size_t>(
                             std::numeric_limits<unsigned>::max()))
                return error_result(
                    std::move(options),
                    "--eq-gb-partition-prepass-bv1-zero-timeout-ms must "
                    "fit in an unsigned integer");
            options.eq_gb_partition_prepass_bv1_zero_timeout_ms =
                static_cast<unsigned>(parsed);
        }
        else if (arg ==
                 "--eq-gb-partition-prepass-bv1-zero-workers")
        {
            std::string error;
            if (!parse_positive_process_count(
                    i, argc, argv, arg,
                    options.eq_gb_partition_prepass_bv1_zero_workers,
                    error))
                return error_result(std::move(options), std::move(error));
            options.eq_gb_partition_prepass_bv1_zero_workers_explicit = true;
        }
        else if (arg ==
                 "--eq-gb-partition-prepass-bv1-zero-backend")
        {
            if (i + 1 >= argc)
                return error_result(
                    std::move(options),
                    arg + " requires z3, boolector, or bitwuzla");
            const std::string value = argv[++i];
            if (value == "z3")
                options.eq_gb_partition_prepass_bv1_zero_backend =
                    Bv1ZeroBackend::Z3;
            else if (value == "boolector")
                options.eq_gb_partition_prepass_bv1_zero_backend =
                    Bv1ZeroBackend::Boolector;
            else if (value == "bitwuzla")
                options.eq_gb_partition_prepass_bv1_zero_backend =
                    Bv1ZeroBackend::Bitwuzla;
            else
                return error_result(
                    std::move(options),
                    arg + " requires z3, boolector, or bitwuzla");
            options.eq_gb_partition_prepass_bv1_zero_backend_explicit = true;
        }
        else if (arg ==
                 "--eq-gb-partition-prepass-bv1-zero-only")
            options.eq_gb_partition_prepass_bv1_zero_only = true;
        else if (arg ==
                 "--eq-gb-partition-prepass-concurrent-widths")
            options.eq_gb_partition_prepass_concurrent_widths = true;
        else if (arg == "--eq-gb-partition-prepass-z3-mpm")
        {
            if (options.eq_gb_partition_prepass_variant !=
                EqGbPartitionPrepassVariant::Default)
                return error_result(
                    std::move(options),
                    "partition-prepass engine options are mutually exclusive");
            options.eq_gb_partition_prepass_variant =
                EqGbPartitionPrepassVariant::Z3Mpm;
        }
        else if (arg == "--eq-gb-partition-prepass-hipr")
        {
            if (options.eq_gb_partition_prepass_variant !=
                EqGbPartitionPrepassVariant::Default)
                return error_result(
                    std::move(options),
                    "partition-prepass engine options are mutually exclusive");
            options.eq_gb_partition_prepass_variant =
                EqGbPartitionPrepassVariant::Hipr;
        }
        else if (arg == "--eq-gb-partition-prepass-ipr")
        {
            if (options.eq_gb_partition_prepass_variant !=
                EqGbPartitionPrepassVariant::Default)
                return error_result(
                    std::move(options),
                    "partition-prepass engine options are mutually exclusive");
            options.eq_gb_partition_prepass_variant =
                EqGbPartitionPrepassVariant::Ipr;
        }
        else if (arg == "--eq-gb-partition-prepass-abipr")
        {
            if (options.eq_gb_partition_prepass_variant !=
                EqGbPartitionPrepassVariant::Default)
                return error_result(
                    std::move(options),
                    "partition-prepass engine options are mutually exclusive");
            options.eq_gb_partition_prepass_variant =
                EqGbPartitionPrepassVariant::Abipr;
        }
        else if (arg == "--eq-gb-partition-prepass-sopr")
        {
            if (options.eq_gb_partition_prepass_variant !=
                EqGbPartitionPrepassVariant::Default)
                return error_result(
                    std::move(options),
                    "partition-prepass engine options are mutually exclusive");
            options.eq_gb_partition_prepass_variant =
                EqGbPartitionPrepassVariant::Sopr;
        }
        else if (arg == "--eq-gb-partition-prepass-hsopr")
        {
            if (options.eq_gb_partition_prepass_variant !=
                EqGbPartitionPrepassVariant::Default)
                return error_result(
                    std::move(options),
                    "partition-prepass engine options are mutually exclusive");
            options.eq_gb_partition_prepass_variant =
                EqGbPartitionPrepassVariant::Hsopr;
        }
        else if (arg == "--eq-gb-partition-prepass-bitwuzla")
        {
            if (options.eq_gb_partition_prepass_variant !=
                EqGbPartitionPrepassVariant::Default)
                return error_result(
                    std::move(options),
                    "partition-prepass engine options are mutually exclusive");
            options.eq_gb_partition_prepass_variant =
                EqGbPartitionPrepassVariant::Bitwuzla;
        }
        else if (arg == "--eq-gb-partition-prepass-boolector")
        {
            if (options.eq_gb_partition_prepass_variant !=
                EqGbPartitionPrepassVariant::Default)
                return error_result(
                    std::move(options),
                    "partition-prepass engine options are mutually exclusive");
            options.eq_gb_partition_prepass_variant =
                EqGbPartitionPrepassVariant::Boolector;
        }
        else if (arg == "--eq-gb-partition-prepass-parallel-bpr")
        {
            if (options.eq_gb_partition_prepass_variant !=
                EqGbPartitionPrepassVariant::Default)
                return error_result(
                    std::move(options),
                    "partition-prepass engine options are mutually exclusive");
            options.eq_gb_partition_prepass_variant =
                EqGbPartitionPrepassVariant::ParallelBpr;
        }
        else if (arg == "--eq-gb-partition-prepass-parallel-workers")
        {
            std::size_t workers = 0;
            std::string error;
            if (!parse_positive_process_count(
                    i, argc, argv, arg, workers, error))
                return error_result(std::move(options), std::move(error));
            options.eq_gb_partition_prepass_parallel_workers = workers;
        }
        else if (arg ==
                 "--eq-gb-partition-prepass-parallel-query-timeout-ms")
        {
            if (i + 1 >= argc)
                return error_result(
                    std::move(options),
                    "--eq-gb-partition-prepass-parallel-query-timeout-ms "
                    "requires one non-negative integer argument");
            const std::string value = argv[++i];
            std::size_t parsed = 0;
            if (!is_unsigned_integer(value) || !parse_size(value, parsed) ||
                parsed > static_cast<std::size_t>(
                             std::numeric_limits<unsigned>::max()))
                return error_result(
                    std::move(options),
                    "--eq-gb-partition-prepass-parallel-query-timeout-ms "
                    "must fit in an unsigned integer");
            options.eq_gb_partition_prepass_parallel_query_timeout_ms =
                static_cast<unsigned>(parsed);
        }
        else if (arg ==
                 "--eq-gb-partition-prepass-parallel-boolector-fallback")
            options.eq_gb_partition_prepass_parallel_boolector_fallback =
                true;
        else if (arg ==
                 "--eq-gb-partition-prepass-parallel-boolector-embedded-global-fallback")
            options.eq_gb_partition_prepass_parallel_boolector_embedded_global_fallback =
                true;
        else if (arg ==
                 "--eq-gb-partition-prepass-parallel-bitwuzla-embedded-global-fallback")
            options.eq_gb_partition_prepass_parallel_bitwuzla_embedded_global_fallback =
                true;
        else if (arg ==
                 "--eq-gb-partition-prepass-parallel-boolector-direct-fallback")
            options.eq_gb_partition_prepass_parallel_boolector_direct_fallback =
                true;
        else if (arg ==
                 "--eq-gb-partition-prepass-parallel-bitwuzla-direct-fallback")
            options.eq_gb_partition_prepass_parallel_bitwuzla_direct_fallback =
                true;
        else if (arg ==
                 "--eq-gb-partition-prepass-parallel-final-validation")
            options.eq_gb_partition_prepass_parallel_final_validation = true;
        else if (arg == "--enable-eq-gb-z3-parallel-candidates")
            options.enable_eq_gb_z3_parallel_candidates = true;
        else if (arg == "--enable-eq-gb-z3-all-bv-constants")
            options.enable_eq_gb_z3_all_bv_constants = true;
        else if (arg == "--eq-gb-z3-validation-batch-size")
        {
            if (i + 1 >= argc)
                return error_result(
                    std::move(options),
                    "--eq-gb-z3-validation-batch-size requires one positive integer argument");
            const std::string value = argv[++i];
            if (!is_unsigned_integer(value))
                return error_result(
                    std::move(options),
                    "--eq-gb-z3-validation-batch-size requires one positive integer argument");
            if (!parse_size(value, options.eq_gb_z3_validation_batch_size))
                return error_result(std::move(options),
                                    "--eq-gb-z3-validation-batch-size is too large");
            if (options.eq_gb_z3_validation_batch_size == 0)
                return error_result(std::move(options),
                                    "--eq-gb-z3-validation-batch-size must be greater than zero");
        }
        else if (arg == "--eq-gb-z3-seeded-candidate-solvers")
        {
            if (i + 1 >= argc)
                return error_result(
                    std::move(options),
                    "--eq-gb-z3-seeded-candidate-solvers requires one non-negative integer argument");
            const std::string value = argv[++i];
            if (!is_unsigned_integer(value))
                return error_result(
                    std::move(options),
                    "--eq-gb-z3-seeded-candidate-solvers requires one non-negative integer argument");
            if (!parse_size(value, options.eq_gb_z3_seeded_candidate_solvers) ||
                options.eq_gb_z3_seeded_candidate_solvers >
                    static_cast<std::size_t>(std::numeric_limits<unsigned>::max()))
            {
                return error_result(std::move(options),
                                    "--eq-gb-z3-seeded-candidate-solvers is too large");
            }
        }
        else if (arg == "--enable-bv-eq-fallback")
            options.enable_bv_eq_fallback = true;
        else if (arg == "--inject-ideal-eq")
        {
            if (i + 2 >= argc)
                return error_result(std::move(options),
                                    "--inject-ideal-eq requires two arguments: <var1> <var2>");
            options.inject_ideal_eq.emplace_back(argv[i + 1], argv[i + 2]);
            i += 2;
        }
        else if (arg == "--enable-eqmod-true-lemmas")
            options.enable_eqmod_true_lemmas = true;
        else if (arg == "--enable-eqmod-true-lemma-lift-antecedents")
            options.enable_eqmod_true_lemma_lift_antecedents = true;
        else if (arg == "--dump-singular")
            options.dump_singular = true;
        else if (arg == "--enable-gb-preprocess")
            options.enable_gb_preprocess = true;
        else if (arg == "--verify-gb-preprocess")
        {
            options.enable_gb_preprocess = true;
            options.verify_gb_preprocess = true;
        }
        else if (arg == "--enable-ideal-rewrite")
            options.enable_ideal_rewrite = true;
        else if (arg == "--eq-gb-true-lemma-processes")
        {
            std::string error;
            std::size_t value = 0;
            if (!parse_positive_process_count(i, argc, argv, arg, value, error))
                return error_result(std::move(options), error);
            options.eq_gb_true_lemma_processes = value;
        }
        else if (arg == "--eq-gb-reuse-base-basis")
            options.eq_gb_reuse_base_basis = true;
        else if (arg == "--eq-gb-refutation-processes")
        {
            std::string error;
            std::size_t value = 0;
            if (!parse_positive_process_count(i, argc, argv, arg, value, error))
                return error_result(std::move(options), error);
            options.eq_gb_refutation_processes = value;
        }
        else if (arg == "--show-model")
            options.show_model_on_terminal = true;
        else if (arg == "--rewrite-log")
            options.rewrite_log_requested = true;
        else if (arg == "--log-conflict-ants")
            options.log_conflict_ants = true;
        else if (arg == "--disable-groebner-ring-order")
            options.use_groebner_ring_var_order = false;
        else if (arg == "--disable-fix-log")
            options.print_fixed_all = false;
        else
        {
            std::string callback_error;
            int option_index = i;
            if (util::parse_eq_callback_option(arg, option_index, argc, argv,
                                               options.eq_callback_options, callback_error))
            {
                i = option_index;
                continue;
            }

            std::string error = "Unknown option: " + arg;
            if (!callback_error.empty())
                error += "\n" + callback_error;
            return error_result(std::move(options), std::move(error), true, true);
        }
    }

    if (options.enable_auto_zero_lemmas &&
        options.enable_auto_zero_lemmas_bv1_callback)
        return error_result(
            std::move(options),
            "auto-zero-lemmas modes are mutually exclusive");

    if ((!options.eq_gb_live_propagate || !options.eq_gb_live_generators) &&
        !options.enable_eq_gb_live)
        return error_result(
            std::move(options),
            "--eq-gb-live-no-propagation and --eq-gb-live-no-generators require --enable-eq-gb-live");
    if (!options.eq_gb_live_seed_models && !options.enable_eq_gb_live)
        return error_result(
            std::move(options),
            "--eq-gb-live-no-seed-models requires --enable-eq-gb-live");
    if (options.eq_gb_live_unified_queue && !options.enable_eq_gb_live)
        return error_result(
            std::move(options),
            "--eq-gb-live-unified-queue requires --enable-eq-gb-live");
    if ((options.eq_gb_live_hybrid ||
         options.eq_gb_live_partition_refinement) &&
        !options.enable_eq_gb_live)
        return error_result(
            std::move(options),
            "--eq-gb-live-hybrid and --eq-gb-live-partition-refinement require --enable-eq-gb-live");
    if (options.eq_gb_live_hybrid &&
        options.eq_gb_live_partition_refinement)
        return error_result(
            std::move(options),
            "--eq-gb-live-hybrid and --eq-gb-live-partition-refinement are mutually exclusive");
    if (options.eq_gb_partition_prepass_propagation &&
        !options.enable_eq_gb_partition_prepass)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-propagation requires --enable-eq-gb-partition-prepass");
    if (options.eq_gb_partition_prepass_workers &&
        !options.enable_eq_gb_partition_prepass)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-workers requires "
            "--enable-eq-gb-partition-prepass");
    if (options.eq_gb_partition_prepass_workers &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::Default)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-workers cannot be combined with "
            "legacy partition engine selectors");
    if (options.eq_gb_partition_prepass_z3_only &&
        !options.eq_gb_partition_prepass_workers)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-z3-only requires "
            "--eq-gb-partition-prepass-workers");
    if (options.eq_gb_partition_prepass_scheduler_explicit &&
        (!options.eq_gb_partition_prepass_workers ||
         *options.eq_gb_partition_prepass_workers < 2))
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-scheduler requires "
            "--eq-gb-partition-prepass-workers N with N >= 2");
    if (options.eq_gb_partition_prepass_all_pairs &&
        !options.enable_eq_gb_partition_prepass)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-all-pairs requires --enable-eq-gb-partition-prepass");
    if (options.eq_gb_partition_prepass_bv1_zero_anchor &&
        !options.enable_eq_gb_partition_prepass)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-bv1-zero-anchor requires --enable-eq-gb-partition-prepass");
    if (options.eq_gb_partition_prepass_bv1_zero_timeout_ms &&
        !options.eq_gb_partition_prepass_bv1_zero_anchor)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-bv1-zero-timeout-ms requires "
            "--eq-gb-partition-prepass-bv1-zero-anchor");
    if ((options.eq_gb_partition_prepass_bv1_zero_workers_explicit ||
         options.eq_gb_partition_prepass_bv1_zero_backend_explicit ||
         options.eq_gb_partition_prepass_bv1_zero_only ||
         options.eq_gb_partition_prepass_concurrent_widths) &&
        !options.eq_gb_partition_prepass_bv1_zero_anchor)
        return error_result(
            std::move(options),
            "BV1 zero workers/backend/only options require "
            "--eq-gb-partition-prepass-bv1-zero-anchor");
    if (options.enable_eq_gb_partition_prepass &&
        options.enable_eq_gb_live)
        return error_result(
            std::move(options),
            "--enable-eq-gb-partition-prepass is incompatible with --enable-eq-gb-live");
    if (options.enable_eq_gb_partition_prepass &&
        options.enable_eq_gb_z3)
        return error_result(
            std::move(options),
            "--enable-eq-gb-partition-prepass is incompatible with --enable-eq-gb-z3");
    if (options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::Default &&
        !options.enable_eq_gb_partition_prepass)
        return error_result(
            std::move(options),
            "partition-prepass engine options require --enable-eq-gb-partition-prepass");
    if (options.eq_gb_partition_prepass_parallel_workers &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::ParallelBpr &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::Bitwuzla &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::Boolector)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-workers requires "
            "--eq-gb-partition-prepass-parallel-bpr, "
            "--eq-gb-partition-prepass-bitwuzla, or "
            "--eq-gb-partition-prepass-boolector");
    if (options.eq_gb_partition_prepass_parallel_query_timeout_ms &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::ParallelBpr &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::Bitwuzla &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::Boolector)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-query-timeout-ms requires "
            "a parallel partition backend");
    if (options.eq_gb_partition_prepass_parallel_boolector_fallback &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::ParallelBpr)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-boolector-fallback requires "
            "--eq-gb-partition-prepass-parallel-bpr");
    if (options.eq_gb_partition_prepass_parallel_boolector_fallback &&
        (!options.eq_gb_partition_prepass_parallel_query_timeout_ms ||
         *options.eq_gb_partition_prepass_parallel_query_timeout_ms == 0))
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-boolector-fallback requires "
            "a non-zero --eq-gb-partition-prepass-parallel-query-timeout-ms");
    if (options.eq_gb_partition_prepass_parallel_boolector_embedded_global_fallback &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::ParallelBpr)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-boolector-embedded-global-fallback "
            "requires --eq-gb-partition-prepass-parallel-bpr");
    if (options.eq_gb_partition_prepass_parallel_boolector_embedded_global_fallback &&
        (!options.eq_gb_partition_prepass_parallel_query_timeout_ms ||
         *options.eq_gb_partition_prepass_parallel_query_timeout_ms == 0))
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-boolector-embedded-global-fallback "
            "requires a non-zero "
            "--eq-gb-partition-prepass-parallel-query-timeout-ms");
    if (options.eq_gb_partition_prepass_parallel_bitwuzla_embedded_global_fallback &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::ParallelBpr)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-bitwuzla-embedded-global-fallback "
            "requires --eq-gb-partition-prepass-parallel-bpr");
    if (options.eq_gb_partition_prepass_parallel_bitwuzla_embedded_global_fallback &&
        (!options.eq_gb_partition_prepass_parallel_query_timeout_ms ||
         *options.eq_gb_partition_prepass_parallel_query_timeout_ms == 0))
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-bitwuzla-embedded-global-fallback "
            "requires a non-zero "
            "--eq-gb-partition-prepass-parallel-query-timeout-ms");
    if (options.eq_gb_partition_prepass_parallel_boolector_direct_fallback &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::ParallelBpr)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-boolector-direct-fallback "
            "requires --eq-gb-partition-prepass-parallel-bpr");
    if (options.eq_gb_partition_prepass_parallel_boolector_direct_fallback &&
        (!options.eq_gb_partition_prepass_parallel_query_timeout_ms ||
         *options.eq_gb_partition_prepass_parallel_query_timeout_ms == 0))
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-boolector-direct-fallback "
            "requires a non-zero "
            "--eq-gb-partition-prepass-parallel-query-timeout-ms");
    if (options.eq_gb_partition_prepass_parallel_bitwuzla_direct_fallback &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::ParallelBpr)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-bitwuzla-direct-fallback "
            "requires "
            "--eq-gb-partition-prepass-parallel-bpr");
    if (options.eq_gb_partition_prepass_parallel_bitwuzla_direct_fallback &&
        (!options.eq_gb_partition_prepass_parallel_query_timeout_ms ||
         *options.eq_gb_partition_prepass_parallel_query_timeout_ms == 0))
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-bitwuzla-direct-fallback "
            "requires a non-zero "
            "--eq-gb-partition-prepass-parallel-query-timeout-ms");
    const unsigned fallback_modes =
        static_cast<unsigned>(
            options.eq_gb_partition_prepass_parallel_boolector_fallback) +
        static_cast<unsigned>(
            options.eq_gb_partition_prepass_parallel_boolector_embedded_global_fallback) +
        static_cast<unsigned>(
            options.eq_gb_partition_prepass_parallel_bitwuzla_embedded_global_fallback) +
        static_cast<unsigned>(
            options.eq_gb_partition_prepass_parallel_boolector_direct_fallback) +
        static_cast<unsigned>(
            options.eq_gb_partition_prepass_parallel_bitwuzla_direct_fallback);
    if (fallback_modes > 1)
        return error_result(
            std::move(options),
            "partition-prepass fallback modes are "
            "mutually exclusive");
    if (options.eq_gb_partition_prepass_parallel_final_validation &&
        options.eq_gb_partition_prepass_variant !=
            EqGbPartitionPrepassVariant::ParallelBpr)
        return error_result(
            std::move(options),
            "--eq-gb-partition-prepass-parallel-final-validation requires "
            "--eq-gb-partition-prepass-parallel-bpr");
    if (options.eq_gb_true_lemma_processes != 0 &&
        !options.enable_eqmod_true_lemmas)
        return error_result(
            std::move(options),
            "--eq-gb-true-lemma-processes requires --enable-eqmod-true-lemmas");
    if (options.enable_eqmod_true_lemma_lift_antecedents &&
        options.eq_gb_true_lemma_processes != 0)
        return error_result(
            std::move(options),
            "--eq-gb-true-lemma-processes is incompatible with "
            "--enable-eqmod-true-lemma-lift-antecedents");
    if (options.enable_eqmod_true_lemma_lift_antecedents &&
        options.eq_gb_reuse_base_basis)
        return error_result(
            std::move(options),
            "--eq-gb-reuse-base-basis is incompatible with "
            "--enable-eqmod-true-lemma-lift-antecedents");
    ParseResult result;
    result.options = std::move(options);
    result.ok = true;
    return result;
}

void print_usage(std::ostream &os, const char *program)
{
    os << "Usage: " << program
       << " <input.smt2> [--ring-detail] [--no-trace]"
          " [--disable-all-false] [--disable-all-true] [--disable-mixed]"
          " [--m-prime]"
          " [--auto-zero-lemmas]"
          " [--auto-zero-lemmas-bv1-callback]"
          " [--no-rewriting] [--no-singular-nf] [--enable-moduli-normalization]"
          " [--preserve-eqmodp1-vars] [--enable-subexpression-rules]"
          " [--enable-raw-poly-power-rules]"
          " [--enable-expression-growth-check]"
          " [--disable-rewrite-cache] [--verify-rewrite-lookups]"
          " [--disable-final-fixed-value-check] [--minimal-fixed-watch]"
          " [--enable-eq-gb-live]"
          " [--eq-gb-live-hybrid]"
          " [--eq-gb-live-partition-refinement]"
          " [--eq-gb-partition-prepass-propagation]"
          " [--eq-gb-live-workers <N>]"
          " [--eq-gb-live-unified-queue]"
          " [--eq-gb-live-no-seed-models]"
          " [--eq-gb-live-no-propagation] [--eq-gb-live-no-generators]"
          " [--enable-eq-gb-partition-prepass]"
          " [--eq-gb-partition-prepass-workers <N>]"
          " [--eq-gb-partition-prepass-z3-only]"
          " [--eq-gb-partition-prepass-scheduler "
          "<auto|persistent|portfolio>]"
          " (legacy partition experiment options remain accepted but deprecated)"
          " [--eq-gb-partition-prepass-all-pairs]"
          " [--eq-gb-partition-prepass-bv1-zero-anchor]"
          " [--eq-gb-partition-prepass-bv1-zero-timeout-ms <N>]"
          " [--eq-gb-partition-prepass-bv1-zero-workers <N>]"
          " [--eq-gb-partition-prepass-bv1-zero-backend <z3|boolector|bitwuzla>]"
          " [--eq-gb-partition-prepass-bv1-zero-only]"
          " [--eq-gb-partition-prepass-concurrent-widths]"
          " [--eq-gb-partition-prepass-z3-mpm]"
          " [--eq-gb-partition-prepass-hipr]"
          " [--eq-gb-partition-prepass-ipr]"
          " [--eq-gb-partition-prepass-abipr]"
          " [--eq-gb-partition-prepass-sopr]"
          " [--eq-gb-partition-prepass-hsopr]"
          " [--eq-gb-partition-prepass-bitwuzla]"
          " [--eq-gb-partition-prepass-boolector]"
          " [--eq-gb-partition-prepass-parallel-bpr]"
          " [--eq-gb-partition-prepass-parallel-workers <N>]"
          " [--eq-gb-partition-prepass-parallel-query-timeout-ms <N>]"
          " [--eq-gb-partition-prepass-parallel-boolector-fallback]"
          " [--eq-gb-partition-prepass-parallel-boolector-embedded-global-fallback]"
          " [--eq-gb-partition-prepass-parallel-bitwuzla-embedded-global-fallback]"
          " [--eq-gb-partition-prepass-parallel-boolector-direct-fallback]"
          " [--eq-gb-partition-prepass-parallel-bitwuzla-direct-fallback]"
          " [--eq-gb-partition-prepass-parallel-final-validation]"
          " [--enable-eq-gb-z3]"
          " [--enable-eq-gb-z3-parallel-candidates]"
          " [--enable-eq-gb-z3-all-bv-constants]"
          " [--eq-gb-z3-validation-batch-size <N>]"
          " [--eq-gb-z3-seeded-candidate-solvers <N>]"
          " [--enable-bv-eq-fallback]"
          " [--enable-eqmod-true-lemmas] [--enable-eqmod-true-lemma-lift-antecedents]"
          " [--dump-singular]"
          " [--enable-gb-preprocess] [--verify-gb-preprocess]"
          " [--enable-ideal-rewrite]"
          " [--eq-gb-true-lemma-processes <N>]"
          " [--eq-gb-reuse-base-basis]"
          " [--eq-gb-refutation-processes <N>]"
       << util::eq_callback_usage()
       << " [--show-model]"
          " [--rewrite-log] [--disable-groebner-ring-order]\n";
}

} // namespace cli
