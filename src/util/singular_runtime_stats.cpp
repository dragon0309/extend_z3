#include "util/singular_runtime_stats.hpp"

#include <algorithm>
#include <mutex>
#include <sys/resource.h>

namespace util::singular
{
namespace
{

std::mutex &statistics_mutex()
{
    static std::mutex value;
    return value;
}

RuntimeStatistics &statistics_storage()
{
    static RuntimeStatistics value;
    return value;
}

OperationTiming subtract_timing(const OperationTiming &after,
                                const OperationTiming &before)
{
    OperationTiming result;
    result.calls = after.calls >= before.calls ? after.calls - before.calls : 0;
    result.elapsed = after.elapsed >= before.elapsed
                         ? after.elapsed - before.elapsed
                         : std::chrono::nanoseconds{0};
    result.bytes = after.bytes >= before.bytes ? after.bytes - before.bytes : 0;
    return result;
}

void merge_timing(OperationTiming &target, const OperationTiming &source)
{
    target.calls += source.calls;
    target.elapsed += source.elapsed;
    target.bytes += source.bytes;
}

} // namespace

void reset_runtime_statistics()
{
    std::lock_guard<std::mutex> lock(statistics_mutex());
    statistics_storage() = RuntimeStatistics{};
}

RuntimeStatistics runtime_statistics()
{
    std::lock_guard<std::mutex> lock(statistics_mutex());
    return statistics_storage();
}

RuntimeStatistics subtract_runtime_statistics(const RuntimeStatistics &after,
                                               const RuntimeStatistics &before)
{
    RuntimeStatistics result;
    result.preprocess = subtract_timing(after.preprocess, before.preprocess);
    result.normal_form = subtract_timing(after.normal_form, before.normal_form);
    result.serialization = subtract_timing(after.serialization, before.serialization);
    result.deserialization = subtract_timing(after.deserialization, before.deserialization);
    result.process_wall = subtract_timing(after.process_wall, before.process_wall);
    result.process_batches = after.process_batches >= before.process_batches
                                 ? after.process_batches - before.process_batches
                                 : 0;
    result.worker_max_rss_kb = after.worker_max_rss_kb;
    return result;
}

void merge_runtime_statistics(const RuntimeStatistics &stats)
{
    std::lock_guard<std::mutex> lock(statistics_mutex());
    RuntimeStatistics &target = statistics_storage();
    merge_timing(target.preprocess, stats.preprocess);
    merge_timing(target.normal_form, stats.normal_form);
    merge_timing(target.serialization, stats.serialization);
    merge_timing(target.deserialization, stats.deserialization);
    merge_timing(target.process_wall, stats.process_wall);
    target.process_batches += stats.process_batches;
    target.worker_max_rss_kb =
        std::max(target.worker_max_rss_kb, stats.worker_max_rss_kb);
}

void record_preprocess(std::chrono::nanoseconds elapsed)
{
    std::lock_guard<std::mutex> lock(statistics_mutex());
    ++statistics_storage().preprocess.calls;
    statistics_storage().preprocess.elapsed += elapsed;
}

void record_normal_form(std::chrono::nanoseconds elapsed)
{
    std::lock_guard<std::mutex> lock(statistics_mutex());
    ++statistics_storage().normal_form.calls;
    statistics_storage().normal_form.elapsed += elapsed;
}

void record_serialization(std::chrono::nanoseconds elapsed,
                          std::uint64_t bytes)
{
    std::lock_guard<std::mutex> lock(statistics_mutex());
    ++statistics_storage().serialization.calls;
    statistics_storage().serialization.elapsed += elapsed;
    statistics_storage().serialization.bytes += bytes;
}

void record_deserialization(std::chrono::nanoseconds elapsed,
                            std::uint64_t bytes)
{
    std::lock_guard<std::mutex> lock(statistics_mutex());
    ++statistics_storage().deserialization.calls;
    statistics_storage().deserialization.elapsed += elapsed;
    statistics_storage().deserialization.bytes += bytes;
}

void record_process_wall(std::chrono::nanoseconds elapsed)
{
    std::lock_guard<std::mutex> lock(statistics_mutex());
    ++statistics_storage().process_wall.calls;
    statistics_storage().process_wall.elapsed += elapsed;
}

void record_process_batch()
{
    std::lock_guard<std::mutex> lock(statistics_mutex());
    ++statistics_storage().process_batches;
}

void record_worker_max_rss_kb(std::size_t rss_kb)
{
    std::lock_guard<std::mutex> lock(statistics_mutex());
    statistics_storage().worker_max_rss_kb =
        std::max(statistics_storage().worker_max_rss_kb, rss_kb);
}

std::size_t current_process_max_rss_kb()
{
    struct rusage usage
    {
    };
    if (getrusage(RUSAGE_SELF, &usage) != 0 || usage.ru_maxrss < 0)
        return 0;
#if defined(__APPLE__)
    return static_cast<std::size_t>(usage.ru_maxrss / 1024);
#else
    return static_cast<std::size_t>(usage.ru_maxrss);
#endif
}

} // namespace util::singular
