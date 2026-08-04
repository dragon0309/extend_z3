#pragma once

#include <z3++.h>

#include <chrono>
#include <cstddef>
#include <memory>
#include <vector>

namespace util
{
class Logger;
}

namespace util::eqgb
{

enum class ValidationStatus
{
    Proved,
    Refuted,
    Unknown
};

struct ValidationResult
{
    std::size_t lhs = 0;
    std::size_t rhs = 0;
    bool direct = false;
    ValidationStatus status = ValidationStatus::Unknown;
    std::chrono::nanoseconds elapsed{0};
};

struct LiveValidatorOptions
{
    std::size_t workers = 4;
    unsigned timeout_ms = 10000;
    std::size_t batch_size = 64;
    bool start_paused = true;
    bool seed_models = true;
    bool unified_queue = false;
};

struct LiveValidatorStatistics
{
    std::size_t callback_candidates = 0;
    std::size_t direct_candidates = 0;
    std::size_t derived_candidates = 0;
    std::size_t duplicate_candidates = 0;
    std::size_t promoted_candidates = 0;
    std::size_t submitted = 0;
    std::size_t direct_submitted = 0;
    std::size_t derived_submitted = 0;
    std::size_t model_pruned = 0;
    std::size_t counterexample_models = 0;
    std::size_t pending = 0;
    std::size_t direct_queued = 0;
    std::size_t derived_queued = 0;
    std::size_t queue_high_water = 0;
    std::size_t tasks_started = 0;
    std::size_t seed_checks = 0;
    std::size_t seed_unsat = 0;
    std::size_t seed_models = 0;
    std::size_t seed_initial_pruned = 0;
    std::size_t seed_late_pruned = 0;
    std::size_t validation_model_pruned = 0;
    std::size_t prefinal_batches = 0;
    std::size_t final_batches = 0;
    std::size_t partial_batches = 0;
    std::size_t regular_batches = 0;
    std::size_t checks = 0;
    std::size_t proved = 0;
    std::size_t refuted = 0;
    std::size_t unknown = 0;
    std::chrono::nanoseconds queue_wait{0};
    std::chrono::nanoseconds max_queue_wait{0};
    std::chrono::nanoseconds seed_time{0};
    std::chrono::nanoseconds check_time{0};
};

class LiveGlobalEqValidator
{
    struct Impl;
    std::unique_ptr<Impl> m_impl;

public:
    LiveGlobalEqValidator(
        z3::context &source_context,
        const std::vector<z3::expr> &constraints,
        const std::vector<z3::expr> &terms,
        const LiveValidatorOptions &options,
        util::Logger *log = nullptr);

    ~LiveGlobalEqValidator();
    LiveGlobalEqValidator(const LiveGlobalEqValidator &) = delete;
    LiveGlobalEqValidator &operator=(const LiveGlobalEqValidator &) = delete;

    // Primary candidates, including direct Main Solver observations and
    // offline clients that do not use the derived-candidate queue.
    bool submit_direct_candidate(std::size_t lhs, std::size_t rhs,
                                 std::size_t scope_depth);
    // Candidates derived only from the Main Solver's scoped callback graph.
    bool submit_derived_candidate(std::size_t lhs, std::size_t rhs,
                                  std::size_t scope_depth);

    // Force worker startup if no full batch opened the gate, rank remaining
    // candidates (with direct candidates first), and allow every partial tail
    // batch to drain at final.
    void release();

    std::vector<ValidationResult> drain_results();
    bool has_results() const;
    // Wait until at least one completed result can be drained, or until all
    // submitted work has reached a terminal state.
    void wait_for_results_or_idle();
    void wait_until_idle();
    bool idle() const;
    LiveValidatorStatistics statistics() const;
};

} // namespace util::eqgb
