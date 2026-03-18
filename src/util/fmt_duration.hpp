#pragma once
#include <chrono>
#include <iomanip>
#include <sstream>
#include <string>

template <class Rep, class Period>
inline std::string fmt_duration(std::chrono::duration<Rep, Period> d)
{
    using namespace std::chrono;

    auto ns = duration_cast<nanoseconds>(d).count();
    long double v = (long double)ns;

    const char *unit = "ns";
    if (ns >= 1000LL && ns < 1000LL * 1000LL)
    {
        v = v / 1000.0L;
        unit = "us";
    }
    else if (ns >= 1000LL * 1000LL && ns < 1000LL * 1000LL * 1000LL)
    {
        v = v / (1000.0L * 1000.0L);
        unit = "ms";
    }
    else if (ns >= 1000LL * 1000LL * 1000LL && ns < 60LL * 1000LL * 1000LL * 1000LL)
    {
        v = v / (1000.0L * 1000.0L * 1000.0L);
        unit = "s";
    }
    else if (ns >= 60LL * 1000LL * 1000LL * 1000LL && ns < 3600LL * 1000LL * 1000LL * 1000LL)
    {
        v = v / (60.0L * 1000.0L * 1000.0L * 1000.0L);
        unit = "min";
    }
    else if (ns >= 3600LL * 1000LL * 1000LL * 1000LL)
    {
        v = v / (3600.0L * 1000.0L * 1000.0L * 1000.0L);
        unit = "h";
    }

    int prec = 3;
    if (std::string(unit) == "ns" || std::string(unit) == "us") prec = 0;
    if (std::string(unit) == "ms") prec = 3;
    if (std::string(unit) == "s")  prec = 3;
    if (std::string(unit) == "min" || std::string(unit) == "h") prec = 2;

    std::ostringstream oss;
    oss << std::fixed << std::setprecision(prec) << (double)v << ' ' << unit;
    return oss.str();
}
