#pragma once

#include <z3++.h>

#include <chrono>
#include <cstddef>
#include <iosfwd>
#include <optional>
#include <string>

#include "util/singular_runtime_stats.hpp"

namespace cli::report
{

using Clock = std::chrono::steady_clock;

class ScopedStreamRedirect
{
    std::ostream &stream_;
    std::streambuf *old_;

public:
    ScopedStreamRedirect(std::ostream &stream, std::streambuf *next);
    ~ScopedStreamRedirect();

    ScopedStreamRedirect(const ScopedStreamRedirect &) = delete;
    ScopedStreamRedirect &operator=(const ScopedStreamRedirect &) = delete;
};

struct AccumulatedTiming
{
    std::size_t calls = 0;
    std::chrono::nanoseconds elapsed{0};

    void reset();

    template <class Rep, class Period>
    void add(std::chrono::duration<Rep, Period> duration)
    {
        ++calls;
        elapsed +=
            std::chrono::duration_cast<std::chrono::nanoseconds>(duration);
    }
};

class ScopedAccumulatedTiming
{
    AccumulatedTiming &timing_;
    Clock::time_point start_;

public:
    explicit ScopedAccumulatedTiming(
        AccumulatedTiming &timing,
        std::optional<Clock::time_point> *first_start = nullptr);
    ~ScopedAccumulatedTiming();

    ScopedAccumulatedTiming(const ScopedAccumulatedTiming &) = delete;
    ScopedAccumulatedTiming &operator=(const ScopedAccumulatedTiming &) = delete;
};

struct Summary
{
    std::string input_file;
    std::string options;
    std::chrono::nanoseconds parse_time{0};
    std::chrono::nanoseconds rewrite_time{0};
    std::chrono::nanoseconds solve_time{0};
    std::chrono::nanoseconds total_time{0};
    std::size_t groebner_calls = 0;
    std::chrono::nanoseconds groebner_time{0};
    std::size_t final_fixed_value_check_calls = 0;
    std::chrono::nanoseconds final_fixed_value_check_time{0};
    util::singular::RuntimeStatistics singular_runtime;
    std::size_t self_max_rss_kb = 0;
    z3::check_result result = z3::unknown;
};

void print_value_row(
    std::ostream &output,
    const std::string &label,
    const std::string &value);

void begin_timed_row(std::ostream &output, const std::string &label);

void finish_timed_row(
    std::ostream &output,
    const std::string &status,
    std::chrono::nanoseconds elapsed,
    std::optional<std::size_t> calls = std::nullopt);

void print_input_section(
    std::ostream &output,
    const std::string &input_file,
    const std::string &options);

void print_summary(
    std::ostream &output,
    const Summary &summary,
    const std::string &terminal_model,
    bool show_model);

} // namespace cli::report
