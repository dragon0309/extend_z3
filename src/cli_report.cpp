#include "cli_report.hpp"

#include <iomanip>
#include <ostream>
#include <sstream>

namespace cli::report
{
namespace
{

std::string format_seconds(std::chrono::nanoseconds duration)
{
    const double seconds = std::chrono::duration<double>(duration).count();
    std::ostringstream output;
    output << std::fixed << std::setprecision(4) << seconds << " seconds";
    return output.str();
}

std::string result_name(z3::check_result result)
{
    switch (result)
    {
    case z3::sat:
        return "sat";
    case z3::unsat:
        return "unsat";
    case z3::unknown:
        return "unknown";
    }
    return "unknown";
}

} // namespace

ScopedStreamRedirect::ScopedStreamRedirect(
    std::ostream &stream,
    std::streambuf *next)
    : stream_(stream), old_(stream.rdbuf(next))
{
}

ScopedStreamRedirect::~ScopedStreamRedirect()
{
    stream_.rdbuf(old_);
}

void AccumulatedTiming::reset()
{
    calls = 0;
    elapsed = std::chrono::nanoseconds{0};
}

ScopedAccumulatedTiming::ScopedAccumulatedTiming(
    AccumulatedTiming &timing,
    std::optional<Clock::time_point> *first_start)
    : timing_(timing), start_(Clock::now())
{
    if (first_start && !*first_start)
        *first_start = start_;
}

ScopedAccumulatedTiming::~ScopedAccumulatedTiming()
{
    timing_.add(Clock::now() - start_);
}

void print_value_row(
    std::ostream &output,
    const std::string &label,
    const std::string &value)
{
    output << std::left << std::setw(49) << label << value << "\n";
}

void begin_timed_row(std::ostream &output, const std::string &label)
{
    output << std::left << std::setw(49) << label;
    output.flush();
}

void finish_timed_row(
    std::ostream &output,
    const std::string &status,
    std::chrono::nanoseconds elapsed,
    std::optional<std::size_t> calls)
{
    std::ostringstream state;
    state << "[" << status << "]";
    if (calls)
        state << " " << *calls << " calls";

    output << std::left << std::setw(28) << state.str()
           << format_seconds(elapsed) << "\n";
    output.flush();
}

void print_input_section(
    std::ostream &output,
    const std::string &input_file,
    const std::string &options)
{
    output << "# Input\n\n";
    print_value_row(output, "Input file:", input_file);
    print_value_row(output, "Options:", options);
    output << "\n# Procedure main\n\n";
    output.flush();
}

void print_summary(
    std::ostream &output,
    const Summary &summary,
    const std::string &terminal_model,
    bool show_model)
{
    begin_timed_row(output, "   Computing Groebner basis:");
    finish_timed_row(
        output, "OK", summary.groebner_time, summary.groebner_calls);
    output << "\n";
    begin_timed_row(output, "   Fixed-value check:");
    finish_timed_row(
        output, "OK", summary.final_fixed_value_check_time,
        summary.final_fixed_value_check_calls);
    begin_timed_row(output, "   GB preprocessing:");
    finish_timed_row(
        output, "OK", summary.singular_runtime.preprocess.elapsed,
        summary.singular_runtime.preprocess.calls);
    begin_timed_row(output, "   Normal forms:");
    finish_timed_row(
        output, "OK", summary.singular_runtime.normal_form.elapsed,
        summary.singular_runtime.normal_form.calls);
    begin_timed_row(output, "   GB serialization:");
    finish_timed_row(
        output, "OK", summary.singular_runtime.serialization.elapsed,
        summary.singular_runtime.serialization.calls);
    begin_timed_row(output, "   GB deserialization:");
    finish_timed_row(
        output, "OK", summary.singular_runtime.deserialization.elapsed,
        summary.singular_runtime.deserialization.calls);
    begin_timed_row(output, "   GB process wall:");
    finish_timed_row(
        output, "OK", summary.singular_runtime.process_wall.elapsed,
        summary.singular_runtime.process_wall.calls);
    print_value_row(
        output, "   GB serialized bytes:",
        std::to_string(summary.singular_runtime.serialization.bytes));
    print_value_row(
        output, "   MaxRSS:",
        "self=" + std::to_string(summary.self_max_rss_kb) +
            " KiB, gb-worker-max=" +
            std::to_string(summary.singular_runtime.worker_max_rss_kb) +
            " KiB");
    output << "\n# Summary\n\n";
    begin_timed_row(output, "Verification result:");
    finish_timed_row(output, result_name(summary.result), summary.total_time);
    if (show_model && !terminal_model.empty())
        output << "\n" << terminal_model;
    output.flush();
}

} // namespace cli::report
