#pragma once

#include <functional>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include <z3++.h>

#include "util/logger.hpp"

namespace util
{

enum class EqRegistrationMode
{
    Existing,
    RingBv,
    AllBv
};

inline const char *eq_registration_mode_name(EqRegistrationMode mode)
{
    switch (mode)
    {
    case EqRegistrationMode::Existing:
        return "existing";
    case EqRegistrationMode::RingBv:
        return "ring-bv";
    case EqRegistrationMode::AllBv:
        return "all-bv";
    }
    return "existing";
}

struct EqCallbackOptions
{
    bool trace_events = false;
    EqRegistrationMode registration = EqRegistrationMode::Existing;
};

inline std::string eq_callback_usage()
{
    return " [--eq-trace] [--eq-registration <existing|ring-bv|all-bv>]";
}

inline bool set_eq_registration_mode(const std::string &name,
                                     EqCallbackOptions &options,
                                     std::string &error)
{
    if (name == "existing")
        options.registration = EqRegistrationMode::Existing;
    else if (name == "ring-bv")
        options.registration = EqRegistrationMode::RingBv;
    else if (name == "all-bv")
        options.registration = EqRegistrationMode::AllBv;
    else
    {
        error = "unknown eq registration mode: " + name;
        return false;
    }
    return true;
}

inline bool parse_eq_callback_option(const std::string &arg,
                                       int &index,
                                       int argc,
                                       char **argv,
                                       EqCallbackOptions &options,
                                       std::string &error)
{
    if (arg == "--eq-trace")
    {
        options.trace_events = true;
        return true;
    }

    const std::string registration_prefix = "--eq-registration=";
    if (arg.rfind(registration_prefix, 0) == 0)
        return set_eq_registration_mode(arg.substr(registration_prefix.size()), options, error);

    if (arg == "--eq-registration")
    {
        if (index + 1 >= argc)
        {
            error = "--eq-registration requires a mode";
            return false;
        }
        ++index;
        return set_eq_registration_mode(argv[index], options, error);
    }

    return false;
}

class EqCallbackTracker
{
    Logger *log_ = nullptr;
    bool emit_summary_ = false;
    std::size_t eq_event_count_ = 0;
    std::size_t fixed_event_count_ = 0;
    std::size_t eq_event_with_unregistered_arg_count_ = 0;
    std::vector<std::string> eq_event_samples_with_unregistered_args_;
    std::size_t event_id_ = 0;
    std::size_t scope_depth_ = 0;

    void event(const std::string &kind, const std::string &details = "")
    {
        ++event_id_;
        std::string message = "event=" + std::to_string(event_id_) +
                              " scope=" + std::to_string(scope_depth_) +
                              " kind=" + kind;
        if (!details.empty())
            message += " " + details;
        LOG_INFO(*log_, "eqtrace", message);
    }

    static std::string yes_no(bool v)
    {
        return v ? "yes" : "no";
    }

    static std::string format_bv_width(const z3::expr &e)
    {
        if (!e.get_sort().is_bv())
            return "-";
        return std::to_string(e.get_sort().bv_size());
    }

public:
    EqCallbackTracker(Logger &log, bool emit_summary)
        : log_(&log), emit_summary_(emit_summary)
    {
    }

    bool trace_enabled(const EqCallbackOptions &options) const
    {
        return options.trace_events;
    }

    void on_push(bool enabled, std::size_t active_equalities)
    {
        if (!enabled)
            return;
        ++scope_depth_;
        event("push", "active_eq=" + std::to_string(active_equalities));
    }

    void on_pop(bool enabled, unsigned n, std::size_t active_equalities)
    {
        if (!enabled)
            return;
        scope_depth_ = n > scope_depth_ ? 0 : scope_depth_ - n;
        event("pop", "count=" + std::to_string(n) +
                         " active_eq=" + std::to_string(active_equalities));
    }

    void on_gb(bool enabled,
               bool begin,
               const std::string &label,
               std::size_t active_equalities,
               std::size_t equality_generators,
               std::size_t total_generators)
    {
        if (!enabled)
            return;
        event(begin ? "gb-begin" : "gb-end",
              "label=" + label +
                  " active_eq=" + std::to_string(active_equalities) +
                  " eq_gens=" + std::to_string(equality_generators) +
                  " generators=" + std::to_string(total_generators));
    }

    void on_fixed(const z3::expr &t, const z3::expr &v, bool trace_all = false)
    {
        ++fixed_event_count_;
        if (trace_all)
            event("fixed", "term=" + t.to_string() + " value=" + v.to_string());
    }

    template <typename IsRegisteredFn, typename FormatFixedFn>
    void on_eq(const z3::expr &x,
               const z3::expr &y,
               IsRegisteredFn &&is_registered,
               FormatFixedFn &&format_fixed_value,
               bool trace_all = false,
               std::size_t active_equalities = 0,
        std::size_t equality_generators = 0)
    {
        ++eq_event_count_;

        const bool x_registered = is_registered(x);
        const bool y_registered = is_registered(y);
        if (trace_all)
            event("eq", "lhs=" + x.to_string() +
                            " rhs=" + y.to_string() +
                            " active_eq=" + std::to_string(active_equalities) +
                            " eq_gens=" + std::to_string(equality_generators));
        if (!(x_registered && y_registered))
        {
            ++eq_event_with_unregistered_arg_count_;
            if (eq_event_samples_with_unregistered_args_.size() < 8)
                eq_event_samples_with_unregistered_args_.push_back(x.to_string() + " == " + y.to_string());
        }

        if (trace_all)
            LOG_TRACE(*log_, "eqcallback",
                      "registered-observed-eq: x=" + x.to_string() +
                          " ; y=" + y.to_string() +
                          " ; x_registered=" + yes_no(x_registered) +
                          " ; y_registered=" + yes_no(y_registered) +
                          " ; x_fixed=" + format_fixed_value(x) +
                          " ; y_fixed=" + format_fixed_value(y) +
                          " ; x_bv_width=" + format_bv_width(x) +
                          " ; y_bv_width=" + format_bv_width(y));
    }

    std::string render_summary() const
    {
        std::ostringstream oss;
        oss << "===== [equality callback summary] =====\n";
        oss << "Total eq() events: " << eq_event_count_ << "\n";
        oss << "Total fixed() events: " << fixed_event_count_ << "\n";
        oss << "eq() events with at least one unregistered argument: " << eq_event_with_unregistered_arg_count_ << "\n";
        if (!eq_event_samples_with_unregistered_args_.empty())
        {
            oss << "Samples with unregistered args:\n";
            for (const auto &sample : eq_event_samples_with_unregistered_args_)
                oss << "  - " << sample << "\n";
        }
        return oss.str();
    }

    void print_summary(std::ostream &os) const
    {
        if (!emit_summary_)
            return;
        const std::string summary = render_summary();
        os << summary;
        LOG_INFO(*log_, "eqcallback", "\n" + summary);
    }

    std::size_t fixed_event_count() const { return fixed_event_count_; }
    std::size_t eq_event_count() const { return eq_event_count_; }
};

} // namespace util
