#pragma once

#include <chrono>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <mutex>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>

namespace util
{

enum class LogLevel : int
{
    Error = 0,
    Warn = 1,
    Info = 2,
    Debug = 3,
    Trace = 4
};

namespace detail
{

inline std::string_view loglevel_name(LogLevel lv)
{
    switch (lv)
    {
    case LogLevel::Error:
        return "ERROR";
    case LogLevel::Warn:
        return "WARN ";
    case LogLevel::Info:
        return "INFO ";
    case LogLevel::Debug:
        return "DEBUG";
    case LogLevel::Trace:
        return "TRACE";
    }
    return "UNKWN";
}

inline void write_log_line(std::ostream &os, LogLevel lv, std::string_view module, std::string_view msg)
{
    os << "[" << loglevel_name(lv) << "]"
       << "[" << std::setw(10) << std::left << module << std::right << "] "
       << msg << "\n";
}

} // namespace detail

class Logger
{
public:
    using clk = std::chrono::steady_clock;

private:
    LogLevel global_ = LogLevel::Trace;
    std::unordered_map<std::string, LogLevel> module_level_;

    bool use_stderr_for_warn_ = true;

    // optional file output (disabled by default)
    std::optional<std::string> file_path_;
    std::ofstream file_;
    bool file_flush_on_write_ = false;
    std::ostream *out_ = &std::cout;
    std::ostream *err_ = &std::cerr;

    mutable std::mutex mu_;

    LogLevel effective_threshold(std::string_view module) const
    {
        auto it = module_level_.find(std::string(module));
        if (it != module_level_.end())
            return it->second;
        return global_;
    }

public:
    Logger() = default;
    Logger(std::ostream &out, std::ostream &err) : out_(&out), err_(&err) {}

    void set_global(LogLevel lv)
    {
        std::lock_guard<std::mutex> lk(mu_);
        global_ = lv;
    }

    LogLevel global_level() const
    {
        std::lock_guard<std::mutex> lk(mu_);
        return global_;
    }

    void set_module(std::string module, LogLevel lv)
    {
        std::lock_guard<std::mutex> lk(mu_);
        module_level_[std::move(module)] = lv;
    }

    void clear_module(std::string_view module)
    {
        std::lock_guard<std::mutex> lk(mu_);
        module_level_.erase(std::string(module));
    }

    void set_warn_to_stderr(bool on)
    {
        std::lock_guard<std::mutex> lk(mu_);
        use_stderr_for_warn_ = on;
    }

    // Open a single txt log file. Disabled by default; call this to enable.
    // append=true: append to existing file; append=false: truncate.
    // flush_on_write=true: flush after every line (safer, slower).
    bool enable_file(const std::string &path, bool append = true, bool flush_on_write = false)
    {
        std::lock_guard<std::mutex> lk(mu_);

        std::ios::openmode mode = std::ios::out;
        mode |= append ? std::ios::app : std::ios::trunc;

        std::ofstream f(path, mode);
        if (!f.is_open())
            return false;

        file_.close();
        file_ = std::move(f);
        file_path_ = path;
        file_flush_on_write_ = flush_on_write;
        return true;
    }

    void disable_file()
    {
        std::lock_guard<std::mutex> lk(mu_);
        file_.close();
        file_path_.reset();
    }

    bool file_enabled() const
    {
        std::lock_guard<std::mutex> lk(mu_);
        return file_.is_open();
    }

    void flush()
    {
        std::lock_guard<std::mutex> lk(mu_);
        if (file_.is_open())
            file_.flush();
        out_->flush();
        err_->flush();
    }

    void log(LogLevel lv, std::string_view module, std::string_view msg)
    {
        std::lock_guard<std::mutex> lk(mu_);

        if (!((int)lv <= (int)effective_threshold(module)))
            return;

        // console
        std::ostream *os = out_;
        if (use_stderr_for_warn_ && ((int)lv <= (int)LogLevel::Warn))
            os = err_;
        detail::write_log_line(*os, lv, module, msg);

        // file (optional)
        if (file_.is_open())
        {
            detail::write_log_line(file_, lv, module, msg);
            if (file_flush_on_write_)
                file_.flush();
        }
    }
};

} // namespace util

// Macros
#define LOG_ERROR(LG, MOD, MSG) (LG).log(::util::LogLevel::Error, (MOD), (MSG))
#define LOG_WARN(LG, MOD, MSG) (LG).log(::util::LogLevel::Warn, (MOD), (MSG))
#define LOG_INFO(LG, MOD, MSG) (LG).log(::util::LogLevel::Info, (MOD), (MSG))
#define LOG_DEBUG(LG, MOD, MSG) (LG).log(::util::LogLevel::Debug, (MOD), (MSG))
#define LOG_TRACE(LG, MOD, MSG) (LG).log(::util::LogLevel::Trace, (MOD), (MSG))
