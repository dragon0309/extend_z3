#include "util/live_global_eq_validator.hpp"

#include <algorithm>
#include <atomic>
#include <condition_variable>
#include <cstdint>
#include <deque>
#include <mutex>
#include <stdexcept>
#include <thread>
#include <tuple>
#include <unordered_map>

#include "util/logger.hpp"

namespace util::eqgb
{

namespace
{

using clk = std::chrono::steady_clock;

std::uint64_t pair_key(std::size_t lhs, std::size_t rhs)
{
    if (rhs < lhs)
        std::swap(lhs, rhs);
    if (lhs > UINT32_MAX || rhs > UINT32_MAX)
        throw std::runtime_error("live equality validator term index exceeds 32 bits");
    return (static_cast<std::uint64_t>(lhs) << 32) |
           static_cast<std::uint64_t>(rhs);
}

struct Task
{
    std::size_t lhs = 0;
    std::size_t rhs = 0;
    bool direct = false;
};

enum class TaskState
{
    Queued,
    Running,
    Done
};

struct TaskRecord
{
    TaskState state = TaskState::Queued;
    bool direct = false;
    std::size_t observations = 1;
    std::size_t min_scope_depth = 0;
    clk::time_point enqueued_at = clk::now();
};

struct WorkerState
{
    std::unique_ptr<z3::context> context;
    std::vector<z3::expr> constraints;
    std::vector<z3::expr> terms;
    std::unique_ptr<z3::solver> solver;
};

struct Counterexample
{
    std::vector<std::string> values;
    bool seed = false;
};

enum class ModelRefutation
{
    None,
    Seed,
    Validation
};

std::unique_ptr<WorkerState> make_worker_state(
    z3::context &source_context,
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms,
    unsigned timeout_ms,
    std::size_t worker_index,
    bool seed_models)
{
    auto worker = std::make_unique<WorkerState>();
    worker->context = std::make_unique<z3::context>();
    worker->constraints.reserve(constraints.size());
    worker->terms.reserve(terms.size());
    for (const z3::expr &constraint : constraints)
        worker->constraints.emplace_back(
            *worker->context,
            Z3_translate((Z3_context)source_context, (Z3_ast)constraint,
                         (Z3_context)*worker->context));
    for (const z3::expr &term : terms)
        worker->terms.emplace_back(
            *worker->context,
            Z3_translate((Z3_context)source_context, (Z3_ast)term,
                         (Z3_context)*worker->context));
    if (seed_models)
    {
        worker->solver = std::make_unique<z3::solver>(*worker->context);
        worker->solver->set("timeout", timeout_ms);
        if (worker_index != 0)
            worker->solver->set("random_seed",
                                static_cast<unsigned>(worker_index));
        for (const z3::expr &constraint : worker->constraints)
            worker->solver->add(constraint);
    }
    return worker;
}

std::vector<std::string> model_fingerprint(WorkerState &worker,
                                           const z3::model &model)
{
    std::vector<std::string> values;
    values.reserve(worker.terms.size());
    for (const z3::expr &term : worker.terms)
        values.push_back(model.eval(term, true).to_string());
    return values;
}

} // namespace

struct LiveGlobalEqValidator::Impl
{
    LiveValidatorOptions options;
    util::Logger *log = nullptr;
    std::vector<std::unique_ptr<WorkerState>> worker_states;
    std::vector<std::thread> threads;

    mutable std::mutex mutex;
    std::condition_variable work_cv;
    std::condition_variable idle_cv;
    std::condition_variable result_cv;
    std::condition_variable initial_models_cv;
    std::deque<Task> direct_queue;
    std::deque<Task> derived_queue;
    std::deque<Task> unified_queue;
    std::unordered_map<std::uint64_t, TaskRecord> records;
    std::vector<Counterexample> counterexamples;
    std::vector<ValidationResult> results;
    std::size_t pending = 0;
    std::size_t direct_queued = 0;
    std::size_t derived_queued = 0;
    std::size_t direct_batches_since_derived = 0;
    std::size_t initial_models_ready = 0;
    std::atomic<bool> results_ready{false};
    bool released = false;
    bool flush_partial_batches = false;
    bool stopping = false;
    LiveValidatorStatistics stats;

    Impl(z3::context &source_context,
         const std::vector<z3::expr> &constraints,
         const std::vector<z3::expr> &terms,
         const LiveValidatorOptions &requested_options,
         util::Logger *logger)
        : options(requested_options), log(logger),
          released(!requested_options.start_paused)
    {
        options.workers = std::max<std::size_t>(1, options.workers);
        options.batch_size = std::max<std::size_t>(1, options.batch_size);
        worker_states.reserve(options.workers);
        for (std::size_t i = 0; i < options.workers; ++i)
            worker_states.push_back(
                make_worker_state(source_context, constraints, terms,
                                  options.timeout_ms, i,
                                  options.seed_models));

        threads.reserve(options.workers);
        for (std::size_t i = 0; i < options.workers; ++i)
            threads.emplace_back([this, i] { worker_loop(i); });
        if (log)
            LOG_INFO(*log, "eqgb",
                     "live global-equality validator started: workers=" +
                         std::to_string(options.workers) +
                         " batch=" + std::to_string(options.batch_size) +
                         " seed_models=" +
                         std::string(options.seed_models ? "on" : "off") +
                         " queue_policy=" +
                         std::string(options.unified_queue
                                         ? "unified"
                                         : "split-direct-derived") +
                         " survivor_policy=origin-64" +
                         " terms=" + std::to_string(terms.size()) +
                         " candidate_source=main-callback");
    }

    ~Impl()
    {
        {
            std::lock_guard<std::mutex> lock(mutex);
            stopping = true;
        }
        work_cv.notify_all();
        idle_cv.notify_all();
        result_cv.notify_all();
        initial_models_cv.notify_all();
        for (std::thread &thread : threads)
            if (thread.joinable())
                thread.join();
    }

    ModelRefutation known_model_refutation(std::size_t lhs,
                                           std::size_t rhs) const
    {
        for (const Counterexample &counterexample : counterexamples)
            if (lhs < counterexample.values.size() &&
                rhs < counterexample.values.size() &&
                counterexample.values[lhs] != counterexample.values[rhs])
                return counterexample.seed ? ModelRefutation::Seed
                                           : ModelRefutation::Validation;
        return ModelRefutation::None;
    }

    bool has_queued_work() const
    {
        return direct_queued != 0 || derived_queued != 0;
    }

    bool has_full_gated_batch() const
    {
        if (options.unified_queue)
        {
            if (direct_queued >= options.batch_size)
                return true;
            return derived_queued >= options.batch_size - direct_queued;
        }
        return direct_queued >= options.batch_size ||
               derived_queued >= options.batch_size;
    }

    bool work_ready() const
    {
        if (!released)
            return false;
        if (flush_partial_batches)
            return has_queued_work();
        return has_full_gated_batch();
    }

    void decrement_queued_count(const TaskRecord &record)
    {
        std::size_t *count = record.direct ? &direct_queued
                                           : &derived_queued;
        if (*count != 0)
            --*count;
    }

    void notify_work_ready()
    {
        if (work_ready())
            work_cv.notify_all();
        else
            work_cv.notify_one();
    }

    bool enqueue_candidate(std::size_t lhs, std::size_t rhs, bool direct,
                           std::size_t scope_depth)
    {
        if (rhs < lhs)
            std::swap(lhs, rhs);
        if (lhs == rhs || worker_states.empty() ||
            lhs >= worker_states.front()->terms.size() ||
            rhs >= worker_states.front()->terms.size())
            return false;

        std::lock_guard<std::mutex> lock(mutex);
        ++stats.callback_candidates;
        if (direct)
            ++stats.direct_candidates;
        else
            ++stats.derived_candidates;
        const std::uint64_t key = pair_key(lhs, rhs);
        auto existing = records.find(key);
        if (existing != records.end())
        {
            ++stats.duplicate_candidates;
            TaskRecord &record = existing->second;
            if (direct)
            {
                ++record.observations;
                record.min_scope_depth =
                    std::min(record.min_scope_depth, scope_depth);
            }
            if (direct && !record.direct)
            {
                const bool queued_derived =
                    record.state == TaskState::Queued;
                record.direct = true;
                ++stats.promoted_candidates;
                if (queued_derived)
                {
                    if (derived_queued != 0)
                        --derived_queued;
                    ++direct_queued;
                    // The unified queue already contains this task.  Split
                    // queues need a new direct entry; their stale derived
                    // entry is discarded when popped.
                    if (!options.unified_queue)
                        direct_queue.push_back({lhs, rhs, true});
                    notify_work_ready();
                }
            }
            return false;
        }

        const ModelRefutation known_refutation =
            known_model_refutation(lhs, rhs);
        if (known_refutation != ModelRefutation::None)
        {
            // A counterexample to a global equality remains valid across all
            // Main Solver scopes.  Keep a terminal record so repeated closure
            // construction does not rescan every known model.
            records.emplace(
                key, TaskRecord{TaskState::Done, direct, 1,
                                scope_depth, clk::now()});
            ++stats.refuted;
            ++stats.model_pruned;
            if (known_refutation == ModelRefutation::Seed)
                ++stats.seed_late_pruned;
            else
                ++stats.validation_model_pruned;
            return false;
        }

        records.emplace(
            key, TaskRecord{TaskState::Queued, direct, 1,
                            scope_depth, clk::now()});
        if (direct)
        {
            if (options.unified_queue)
                unified_queue.push_back({lhs, rhs, true});
            else
                direct_queue.push_back({lhs, rhs, true});
            ++direct_queued;
            ++stats.direct_submitted;
        }
        else
        {
            if (options.unified_queue)
                unified_queue.push_back({lhs, rhs, false});
            else
                derived_queue.push_back({lhs, rhs, false});
            ++derived_queued;
            ++stats.derived_submitted;
        }
        ++pending;
        ++stats.submitted;
        stats.queue_high_water = std::max(stats.queue_high_water, pending);
        if (!released && has_full_gated_batch())
            released = true;
        notify_work_ready();
        return true;
    }

    void add_counterexample(std::vector<std::string> values, bool seed)
    {
        std::lock_guard<std::mutex> lock(mutex);
        counterexamples.push_back({std::move(values), seed});
        ++stats.counterexample_models;
        if (seed)
            ++stats.seed_models;

        // Mark queued tasks refuted eagerly. Stale queue entries are skipped by
        // pop_task; running batches finish against their own model.
        const auto &latest = counterexamples.back().values;
        for (auto &[key, record] : records)
        {
            if (record.state != TaskState::Queued)
                continue;
            const std::size_t lhs = static_cast<std::size_t>(key >> 32);
            const std::size_t rhs = static_cast<std::size_t>(key & UINT32_MAX);
            if (lhs >= latest.size() || rhs >= latest.size() ||
                latest[lhs] == latest[rhs])
                continue;
            decrement_queued_count(record);
            record.state = TaskState::Done;
            if (pending != 0)
                --pending;
            ++stats.refuted;
            ++stats.model_pruned;
            if (seed)
                ++stats.seed_initial_pruned;
            else
                ++stats.validation_model_pruned;
        }
        notify_idle_if_ready();
    }

    void notify_idle_if_ready()
    {
        if (pending == 0)
        {
            idle_cv.notify_all();
            result_cv.notify_all();
        }
    }

    bool pop_task_from(std::deque<Task> &queue, bool enforce_direct,
                       bool direct, Task &task)
    {
        while (!queue.empty())
        {
            task = queue.front();
            queue.pop_front();
            auto found = records.find(pair_key(task.lhs, task.rhs));
            if (found == records.end() ||
                found->second.state != TaskState::Queued ||
                (enforce_direct && found->second.direct != direct))
                continue;
            TaskRecord &record = found->second;
            decrement_queued_count(record);
            record.state = TaskState::Running;
            task.direct = record.direct;
            const std::chrono::nanoseconds wait =
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                    clk::now() - record.enqueued_at);
            stats.queue_wait += wait;
            stats.max_queue_wait = std::max(stats.max_queue_wait, wait);
            ++stats.tasks_started;
            return true;
        }
        return false;
    }

    bool pop_task(Task &task, bool &direct_batch)
    {
        // Direct callback observations have much higher proof yield than
        // transitive closure candidates.  Give them priority, but service one
        // derived batch after four direct batches to avoid starvation.
        const bool allow_partial = flush_partial_batches;
        const bool direct_ready =
            direct_queued != 0 &&
            (allow_partial || direct_queued >= options.batch_size);
        const bool derived_ready =
            derived_queued != 0 &&
            (allow_partial || derived_queued >= options.batch_size);
        const bool prefer_direct =
            direct_ready && (!derived_ready || direct_batches_since_derived < 4);
        if (prefer_direct && pop_task_from(direct_queue, true, true, task))
        {
            direct_batch = true;
            return true;
        }
        if (derived_ready && pop_task_from(derived_queue, true, false, task))
        {
            direct_batch = false;
            return true;
        }
        if (direct_ready && pop_task_from(direct_queue, true, true, task))
        {
            direct_batch = true;
            return true;
        }
        return false;
    }

    void finish_task(const Task &task, ValidationStatus status,
                     std::chrono::nanoseconds elapsed)
    {
        const std::uint64_t key = pair_key(task.lhs, task.rhs);
        auto found = records.find(key);
        if (found == records.end() || found->second.state == TaskState::Done)
            return;
        TaskRecord &record = found->second;
        record.state = TaskState::Done;
        results.push_back({task.lhs, task.rhs, record.direct, status, elapsed});
        results_ready.store(true, std::memory_order_release);
        result_cv.notify_all();
        if (status == ValidationStatus::Proved)
            ++stats.proved;
        else if (status == ValidationStatus::Refuted)
            ++stats.refuted;
        else
            ++stats.unknown;
        if (pending != 0)
            --pending;
    }

    void validate_tasks(WorkerState &worker, std::vector<Task> tasks)
    {
        if (tasks.empty())
            return;

        z3::check_result check = z3::unknown;
        std::chrono::nanoseconds elapsed{0};
        try
        {
            // Keep validation checks isolated. Reusing one incremental solver
            // across many unrelated SAT disjunctions caused severe state
            // accumulation; the static BV prover's fresh-per-batch strategy is
            // substantially faster on these formulas.
            z3::solver validator(*worker.context);
            validator.set("timeout", options.timeout_ms);
            for (const z3::expr &constraint : worker.constraints)
                validator.add(constraint);
            z3::expr_vector differences(*worker.context);
            for (const Task &task : tasks)
                differences.push_back(worker.terms[task.lhs] !=
                                      worker.terms[task.rhs]);
            validator.add(z3::mk_or(differences));
            const auto started = clk::now();
            check = validator.check();
            elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - started);
            {
                std::lock_guard<std::mutex> lock(mutex);
                ++stats.checks;
                stats.check_time += elapsed;
            }

            if (check == z3::sat)
            {
                z3::model model = validator.get_model();
                std::vector<std::string> values =
                    model_fingerprint(worker, model);
                std::vector<Task> survivors;
                {
                    std::lock_guard<std::mutex> lock(mutex);
                    for (const Task &task : tasks)
                        if (values[task.lhs] != values[task.rhs])
                            finish_task(task, ValidationStatus::Refuted,
                                        elapsed);
                        else
                            survivors.push_back(task);
                    notify_idle_if_ready();
                }
                add_counterexample(std::move(values), false);

                // Do not recursively validate a shrinking survivor set in
                // isolation. Requeue survivors so they coalesce with later
                // candidates into full 64-candidate batches. The split policy
                // returns them to their origin; the unified policy mixes both
                // origins while retaining the record's direct metadata.
                {
                    std::lock_guard<std::mutex> lock(mutex);
                    for (const Task &task : survivors)
                    {
                        auto found = records.find(pair_key(task.lhs, task.rhs));
                        if (found == records.end() ||
                            found->second.state != TaskState::Running)
                            continue;
                        TaskRecord &record = found->second;
                        const ModelRefutation refutation =
                            known_model_refutation(task.lhs, task.rhs);
                        if (refutation != ModelRefutation::None)
                        {
                            finish_task(task, ValidationStatus::Refuted,
                                        elapsed);
                            ++stats.model_pruned;
                            if (refutation == ModelRefutation::Seed)
                                ++stats.seed_late_pruned;
                            else
                                ++stats.validation_model_pruned;
                            continue;
                        }
                        record.state = TaskState::Queued;
                        record.enqueued_at = clk::now();
                        if (record.direct)
                        {
                            ++direct_queued;
                        }
                        else
                        {
                            ++derived_queued;
                        }
                        if (options.unified_queue)
                            unified_queue.push_back(
                                {task.lhs, task.rhs, record.direct});
                        else if (record.direct)
                            direct_queue.push_back(
                                {task.lhs, task.rhs, true});
                        else
                            derived_queue.push_back(
                                {task.lhs, task.rhs, false});
                    }
                    notify_idle_if_ready();
                }
                work_cv.notify_all();
                return;
            }
        }
        catch (...)
        {
            check = z3::unknown;
        }

        if (check == z3::unknown && tasks.size() > 1)
        {
            // A timeout for a disjunction does not make every member unknown.
            // Bisect until smaller batches become decidable.
            const std::size_t middle = tasks.size() / 2;
            std::vector<Task> right(tasks.begin() +
                                        static_cast<std::ptrdiff_t>(middle),
                                    tasks.end());
            tasks.erase(tasks.begin() + static_cast<std::ptrdiff_t>(middle),
                        tasks.end());
            validate_tasks(worker, std::move(tasks));
            validate_tasks(worker, std::move(right));
            return;
        }

        const ValidationStatus status =
            check == z3::unsat ? ValidationStatus::Proved
                               : ValidationStatus::Unknown;
        {
            std::lock_guard<std::mutex> lock(mutex);
            for (const Task &task : tasks)
                finish_task(task, status, elapsed);
            notify_idle_if_ready();
        }
    }

    void worker_loop(std::size_t worker_index)
    {
        WorkerState &worker = *worker_states[worker_index];
        {
            std::unique_lock<std::mutex> lock(mutex);
            work_cv.wait(lock, [this] { return stopping || released; });
            if (stopping)
                return;
        }

        if (options.seed_models)
        {
            // Match the static BV prover's strongest cheap filter: obtain
            // several seed-diverse base models before spending time on
            // equality proofs. A barrier ensures no worker starts a costly
            // validation batch before every initial model has pruned the
            // shared queue.
            const auto seed_started = clk::now();
            z3::check_result seed_result = z3::unknown;
            try
            {
                seed_result = worker.solver->check();
                if (seed_result == z3::sat)
                    add_counterexample(model_fingerprint(
                                           worker, worker.solver->get_model()),
                                       true);
            }
            catch (...)
            {
                seed_result = z3::unknown;
            }
            const std::chrono::nanoseconds seed_elapsed =
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                    clk::now() - seed_started);
            {
                std::unique_lock<std::mutex> lock(mutex);
                ++stats.seed_checks;
                stats.seed_time += seed_elapsed;
                ++initial_models_ready;
                if (initial_models_ready == worker_states.size())
                    initial_models_cv.notify_all();
                else
                    initial_models_cv.wait(lock, [this] {
                        return stopping ||
                               initial_models_ready == worker_states.size();
                    });
                if (stopping)
                    return;
            }
        }

        while (true)
        {
            std::vector<Task> batch;
            {
                std::unique_lock<std::mutex> lock(mutex);
                work_cv.wait(lock, [this] {
                    return stopping || work_ready();
                });
                if (stopping)
                    return;
                Task task;
                bool direct_batch = false;
                if (options.unified_queue)
                {
                    if (!pop_task_from(unified_queue, false, false, task))
                        continue;
                    batch.push_back(task);
                    while (batch.size() < options.batch_size &&
                           pop_task_from(unified_queue, false, false, task))
                        batch.push_back(task);
                }
                else
                {
                    if (!pop_task(task, direct_batch))
                        continue;
                    batch.push_back(task);
                    std::deque<Task> &selected_queue =
                        direct_batch ? direct_queue : derived_queue;
                    while (batch.size() < options.batch_size &&
                           pop_task_from(selected_queue, true, direct_batch,
                                         task))
                        batch.push_back(task);
                    if (direct_batch)
                        ++direct_batches_since_derived;
                    else
                        direct_batches_since_derived = 0;
                }
                ++stats.regular_batches;
                if (flush_partial_batches)
                    ++stats.final_batches;
                else
                    ++stats.prefinal_batches;
                if (batch.size() < options.batch_size)
                    ++stats.partial_batches;
            }

            validate_tasks(worker, std::move(batch));
        }
    }

    bool submit_callback(std::size_t lhs, std::size_t rhs,
                         std::size_t scope_depth)
    {
        return enqueue_candidate(lhs, rhs, true, scope_depth);
    }

    bool submit_derived(std::size_t lhs, std::size_t rhs,
                        std::size_t scope_depth)
    {
        return enqueue_candidate(lhs, rhs, false, scope_depth);
    }

    void release()
    {
        {
            std::lock_guard<std::mutex> lock(mutex);
            auto rank_direct = [this](const Task &lhs, const Task &rhs) {
                const TaskRecord &a = records.at(pair_key(lhs.lhs, lhs.rhs));
                const TaskRecord &b = records.at(pair_key(rhs.lhs, rhs.rhs));
                if (a.min_scope_depth != b.min_scope_depth)
                    return a.min_scope_depth < b.min_scope_depth;
                if (a.observations != b.observations)
                    return a.observations > b.observations;
                return pair_key(lhs.lhs, lhs.rhs) <
                       pair_key(rhs.lhs, rhs.rhs);
            };
            if (options.unified_queue)
            {
                std::vector<Task> ranked(unified_queue.begin(),
                                         unified_queue.end());
                std::stable_sort(
                    ranked.begin(), ranked.end(),
                    [this, &rank_direct](const Task &lhs, const Task &rhs) {
                        const TaskRecord &a =
                            records.at(pair_key(lhs.lhs, lhs.rhs));
                        const TaskRecord &b =
                            records.at(pair_key(rhs.lhs, rhs.rhs));
                        if (a.direct != b.direct)
                            return a.direct;
                        if (!a.direct)
                            return false;
                        return rank_direct(lhs, rhs);
                    });
                unified_queue.assign(ranked.begin(), ranked.end());
            }
            else
            {
                std::vector<Task> ranked(direct_queue.begin(),
                                         direct_queue.end());
                std::sort(ranked.begin(), ranked.end(), rank_direct);
                direct_queue.assign(ranked.begin(), ranked.end());
            }
            released = true;
            flush_partial_batches = true;
        }
        work_cv.notify_all();
    }
};

LiveGlobalEqValidator::LiveGlobalEqValidator(
    z3::context &source_context,
    const std::vector<z3::expr> &constraints,
    const std::vector<z3::expr> &terms,
    const LiveValidatorOptions &options,
    util::Logger *log)
    : m_impl(std::make_unique<Impl>(source_context, constraints, terms,
                                    options, log))
{
}

LiveGlobalEqValidator::~LiveGlobalEqValidator() = default;

bool LiveGlobalEqValidator::submit_callback_candidate(
    std::size_t lhs, std::size_t rhs, std::size_t scope_depth)
{
    return m_impl->submit_callback(lhs, rhs, scope_depth);
}

bool LiveGlobalEqValidator::submit_derived_candidate(
    std::size_t lhs, std::size_t rhs, std::size_t scope_depth)
{
    return m_impl->submit_derived(lhs, rhs, scope_depth);
}

void LiveGlobalEqValidator::release()
{
    m_impl->release();
}

std::vector<ValidationResult> LiveGlobalEqValidator::drain_results()
{
    std::lock_guard<std::mutex> lock(m_impl->mutex);
    std::vector<ValidationResult> output;
    output.swap(m_impl->results);
    m_impl->results_ready.store(false, std::memory_order_release);
    std::sort(output.begin(), output.end(), [](const auto &lhs, const auto &rhs) {
        return std::tie(lhs.lhs, lhs.rhs) < std::tie(rhs.lhs, rhs.rhs);
    });
    return output;
}

bool LiveGlobalEqValidator::has_results() const
{
    return m_impl->results_ready.load(std::memory_order_acquire);
}

void LiveGlobalEqValidator::wait_for_results_or_idle()
{
    std::unique_lock<std::mutex> lock(m_impl->mutex);
    m_impl->result_cv.wait(lock, [this] {
        return m_impl->stopping || !m_impl->results.empty() ||
               m_impl->pending == 0;
    });
}

void LiveGlobalEqValidator::wait_until_idle()
{
    std::unique_lock<std::mutex> lock(m_impl->mutex);
    m_impl->idle_cv.wait(lock, [this] {
        return m_impl->stopping || m_impl->pending == 0;
    });
}

bool LiveGlobalEqValidator::idle() const
{
    std::lock_guard<std::mutex> lock(m_impl->mutex);
    return m_impl->pending == 0;
}

LiveValidatorStatistics LiveGlobalEqValidator::statistics() const
{
    std::lock_guard<std::mutex> lock(m_impl->mutex);
    LiveValidatorStatistics output = m_impl->stats;
    output.pending = m_impl->pending;
    output.direct_queued = m_impl->direct_queued;
    output.derived_queued = m_impl->derived_queued;
    return output;
}

} // namespace util::eqgb
