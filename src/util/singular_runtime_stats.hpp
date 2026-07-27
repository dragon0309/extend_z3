#pragma once

#include <chrono>
#include <cstddef>
#include <cstdint>

namespace util::singular
{

struct OperationTiming
{
    std::size_t calls = 0;
    std::chrono::nanoseconds elapsed{0};
    std::uint64_t bytes = 0;
};

struct RuntimeStatistics
{
    OperationTiming preprocess;
    OperationTiming normal_form;
    OperationTiming serialization;
    OperationTiming deserialization;
    OperationTiming process_wall;
    std::size_t process_batches = 0;
    std::size_t worker_max_rss_kb = 0;
};

void reset_runtime_statistics();
RuntimeStatistics runtime_statistics();
RuntimeStatistics subtract_runtime_statistics(const RuntimeStatistics &after,
                                               const RuntimeStatistics &before);
void merge_runtime_statistics(const RuntimeStatistics &stats);

void record_preprocess(std::chrono::nanoseconds elapsed);
void record_normal_form(std::chrono::nanoseconds elapsed);
void record_serialization(std::chrono::nanoseconds elapsed,
                          std::uint64_t bytes);
void record_deserialization(std::chrono::nanoseconds elapsed,
                            std::uint64_t bytes);
void record_process_wall(std::chrono::nanoseconds elapsed);
void record_process_batch();
void record_worker_max_rss_kb(std::size_t rss_kb);

std::size_t current_process_max_rss_kb();

} // namespace util::singular
