#pragma once
#include <chrono>
#include <iomanip>
#include <limits>
#include <sstream>
#include <string>

namespace util
{
namespace detail
{

struct DurationFormat
{
    const char *unit;
    long double scale;
    int precision;
};

inline constexpr long double kNs = 1.0L;
inline constexpr long double kUs = 1000.0L;
inline constexpr long double kMs = 1000.0L * 1000.0L;
inline constexpr long double kS = 1000.0L * 1000.0L * 1000.0L;
inline constexpr long double kMin = 60.0L * kS;
inline constexpr long double kHour = 60.0L * kMin;

inline DurationFormat choose_duration_format(long double abs_ns)
{
    if (abs_ns >= kHour)
        return {"h", kHour, 2};
    if (abs_ns >= kMin)
        return {"min", kMin, 2};
    if (abs_ns >= kS)
        return {"s", kS, 3};
    if (abs_ns >= kMs)
        return {"ms", kMs, 3};
    if (abs_ns >= kUs)
        return {"us", kUs, 0};
    return {"ns", kNs, 0};
}

inline long double abs_nanoseconds(std::chrono::nanoseconds d)
{
    const auto ns = d.count();
    if (ns >= 0)
        return static_cast<long double>(ns);
    if (ns == (std::numeric_limits<std::chrono::nanoseconds::rep>::min)())
        return static_cast<long double>((std::numeric_limits<std::chrono::nanoseconds::rep>::max)()) + 1.0L;
    return static_cast<long double>(-ns);
}

} // namespace detail

inline std::string fmt_duration(std::chrono::nanoseconds d)
{
    const long double abs_ns = detail::abs_nanoseconds(d);
    const detail::DurationFormat fmt = detail::choose_duration_format(abs_ns);
    long double value = abs_ns / fmt.scale;
    if (d.count() < 0)
        value = -value;

    std::ostringstream oss;
    oss << std::fixed << std::setprecision(fmt.precision)
        << static_cast<double>(value) << ' ' << fmt.unit;
    return oss.str();
}

template <class Rep, class Period>
inline std::string fmt_duration(std::chrono::duration<Rep, Period> d)
{
    return fmt_duration(std::chrono::duration_cast<std::chrono::nanoseconds>(d));
}

} // namespace util
