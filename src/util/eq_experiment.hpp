#pragma once

#include <functional>
#include <optional>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include <z3++.h>

#include "util/logger.hpp"

namespace util
{

struct EqExperimentOptions
{
    bool ntt_red_mul = false;
    bool bv_indirect = false;
    bool bool_indirect = false;
    bool bool_indirect_3 = false;
    bool bool_indirect_4 = false;
    bool unconstrained_bool = false;

    bool enabled() const
    {
        return ntt_red_mul || bv_indirect || bool_indirect || bool_indirect_3 || bool_indirect_4 || unconstrained_bool;
    }
};

inline std::string eq_experiment_usage()
{
    return " [--eqexp <ntt-red-mul|bv-indirect|bool-indirect|bool-indirect-3|bool-indirect-4|unconstrained-bool>]";
}

inline bool enable_eq_experiment(const std::string &name,
                                 EqExperimentOptions &options,
                                 std::string &error)
{
    if (name == "ntt-red-mul")
    {
        options.ntt_red_mul = true;
        return true;
    }
    if (name == "bv-indirect")
    {
        options.bv_indirect = true;
        return true;
    }
    if (name == "bool-indirect")
    {
        options.bool_indirect = true;
        return true;
    }
    if (name == "bool-indirect-3")
    {
        options.bool_indirect_3 = true;
        return true;
    }
    if (name == "bool-indirect-4")
    {
        options.bool_indirect_4 = true;
        return true;
    }
    if (name == "unconstrained-bool")
    {
        options.unconstrained_bool = true;
        return true;
    }
    if (name == "all")
    {
        options.ntt_red_mul = true;
        options.bv_indirect = true;
        options.bool_indirect = true;
        options.bool_indirect_3 = true;
        options.bool_indirect_4 = true;
        options.unconstrained_bool = true;
        return true;
    }

    error = "unknown eq experiment: " + name;
    return false;
}

inline bool parse_eq_experiment_option(const std::string &arg,
                                       int &index,
                                       int argc,
                                       char **argv,
                                       EqExperimentOptions &options,
                                       std::string &error)
{
    const std::string prefix = "--eqexp=";
    if (arg.rfind(prefix, 0) == 0)
        return enable_eq_experiment(arg.substr(prefix.size()), options, error);

    if (arg == "--eqexp")
    {
        if (index + 1 >= argc)
        {
            error = "--eqexp requires an experiment name";
            return false;
        }
        ++index;
        return enable_eq_experiment(argv[index], options, error);
    }

    return false;
}

inline std::optional<z3::expr> build_manual_eqp_red0_1_mulLymm8_0_1_term(z3::context &ctx,
                                                                         const std::vector<z3::expr> &eqps)
{
    if (eqps.empty())
        return std::nullopt;

    z3::sort poly_sort = eqps.front().arg(0).get_sort();
    z3::func_decl pconst_decl = ctx.function("PConst", ctx.int_sort(), poly_sort);
    z3::func_decl ubv_to_int_decl = ctx.function("ubv_to_int", ctx.bv_sort(16), ctx.int_sort());
    z3::func_decl eqp_decl = ctx.function("eqP", poly_sort, poly_sort, ctx.bool_sort());
    z3::expr red0_1 = ctx.bv_const("red_0_1", 16);
    z3::expr mulLymm8_0_1 = ctx.bv_const("mulLymm8_0_1", 16);
    z3::expr lhs_poly = pconst_decl(ubv_to_int_decl(red0_1));
    z3::expr rhs_poly = pconst_decl(ubv_to_int_decl(mulLymm8_0_1));
    return eqp_decl(lhs_poly, rhs_poly);
}

class EqExperimentTracker
{
    struct ObservedTerm
    {
        std::string experiment;
        std::string display_name;
        z3::expr term;
        bool registered = false;
        bool fixed_seen = false;
        std::string fixed_value = "-";
        bool seen_in_eq = false;
        unsigned bv_width = 0;
    };

    struct WatchedPair
    {
        std::string label;
        Z3_ast lhs = nullptr;
        Z3_ast rhs = nullptr;
        bool observed = false;
    };

    Logger *log_ = nullptr;
    bool emit_summary_ = false;
    std::vector<ObservedTerm> terms_;
    std::unordered_map<Z3_ast, std::size_t> term_index_;
    std::vector<WatchedPair> watched_pairs_;
    std::size_t eq_event_count_ = 0;
    std::size_t eq_event_with_unregistered_arg_count_ = 0;
    std::vector<std::string> eq_event_samples_with_unregistered_args_;

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

    void add_term(const std::string &experiment,
                  const std::string &display_name,
                  const z3::expr &term)
    {
        ObservedTerm row{experiment, display_name, term, false, false, "-", false, 0};
        if (term.get_sort().is_bv())
            row.bv_width = term.get_sort().bv_size();
        term_index_[(Z3_ast)term] = terms_.size();
        terms_.push_back(row);
    }

    template <typename RegisterFn>
    void track_registered_term(const std::string &experiment,
                               const std::string &display_name,
                               const z3::expr &term,
                               RegisterFn &&register_term)
    {
        add_term(experiment, display_name, term);
        ObservedTerm &row = terms_.back();
        register_term(row.term);
        row.registered = true;
        LOG_INFO(*log_, "eqexp",
                 "registered experiment term: " + row.experiment +
                     " :: " + row.display_name +
                     " :: sort=" + row.term.get_sort().to_string());
    }

    void watch_pair(const std::string &label, const z3::expr &lhs, const z3::expr &rhs)
    {
        watched_pairs_.push_back(WatchedPair{label, (Z3_ast)lhs, (Z3_ast)rhs, false});
    }

    void mark_eq_pair_if_watched(const z3::expr &x, const z3::expr &y)
    {
        const Z3_ast xa = (Z3_ast)x;
        const Z3_ast ya = (Z3_ast)y;
        for (auto &pair : watched_pairs_)
        {
            if ((xa == pair.lhs && ya == pair.rhs) ||
                (xa == pair.rhs && ya == pair.lhs))
            {
                pair.observed = true;
            }
        }
    }

    void note_eq_arg(const z3::expr &e)
    {
        auto it = term_index_.find((Z3_ast)e);
        if (it == term_index_.end())
            return;
        terms_[it->second].seen_in_eq = true;
    }

    template <typename RegisterFn>
    void register_ntt_red_mul(z3::context &ctx,
                              const std::vector<z3::expr> &eqps,
                              RegisterFn &&register_term)
    {
        z3::expr red = ctx.bv_const("red_0_1", 16);
        z3::expr mul = ctx.bv_const("mulLymm8_0_1", 16);

        track_registered_term("ntt-red-mul", "red_0_1", red, register_term);
        track_registered_term("ntt-red-mul", "mulLymm8_0_1", mul, register_term);
        watch_pair("eq(red_0_1, mulLymm8_0_1)", red, mul);

        z3::expr bv_eq = (red == mul);
        track_registered_term("ntt-red-mul",
                              "(= red_0_1 mulLymm8_0_1)",
                              bv_eq,
                              register_term);

        if (auto manual_eqp = build_manual_eqp_red0_1_mulLymm8_0_1_term(ctx, eqps))
        {
            track_registered_term("ntt-red-mul",
                                  "(eqP (PConst (bv2nat red_0_1)) (PConst (bv2nat mulLymm8_0_1)))",
                                  *manual_eqp,
                                  register_term);
        }
        else
        {
            LOG_INFO(*log_, "eqexp",
                     "skipped ntt-red-mul eqP tracking because no eqP declarations were found");
        }
    }

    template <typename RegisterFn>
    void register_bv_indirect(z3::context &ctx, RegisterFn &&register_term)
    {
        z3::expr red = ctx.bv_const("red_0_1", 16);
        z3::expr mul = ctx.bv_const("mulLymm8_0_1", 16);
        track_registered_term("bv-indirect", "red_0_1", red, register_term);
        track_registered_term("bv-indirect", "mulLymm8_0_1", mul, register_term);
        watch_pair("eq(red_0_1, mulLymm8_0_1)", red, mul);
    }

    template <typename RegisterFn>
    void register_bool_indirect(z3::context &ctx, RegisterFn &&register_term)
    {
        std::vector<z3::expr> terms;
        terms.push_back(ctx.bool_const("bool_lhs"));
        terms.push_back(ctx.bool_const("bool_rhs"));
        register_bool_equivalence_terms("bool-indirect", terms, register_term);
    }

    template <typename RegisterFn>
    void register_bool_indirect_3(z3::context &ctx, RegisterFn &&register_term)
    {
        std::vector<z3::expr> terms;
        terms.push_back(ctx.bool_const("bool_a"));
        terms.push_back(ctx.bool_const("bool_b"));
        terms.push_back(ctx.bool_const("bool_c"));
        register_bool_equivalence_terms("bool-indirect-3", terms, register_term);
    }

    template <typename RegisterFn>
    void register_bool_indirect_4(z3::context &ctx, RegisterFn &&register_term)
    {
        std::vector<z3::expr> terms;
        terms.push_back(ctx.bool_const("bool_a"));
        terms.push_back(ctx.bool_const("bool_b"));
        terms.push_back(ctx.bool_const("bool_c"));
        terms.push_back(ctx.bool_const("bool_d"));
        register_bool_equivalence_terms("bool-indirect-4", terms, register_term);
    }

    template <typename RegisterFn>
    void register_unconstrained_bool(z3::context &ctx, RegisterFn &&register_term)
    {
        z3::func_decl pred = ctx.function("P", ctx.int_sort(), ctx.bool_sort());

        track_registered_term("unconstrained-bool", "free_bool_0", ctx.bool_const("free_bool_0"), register_term);
        track_registered_term("unconstrained-bool", "free_bool_1", ctx.bool_const("free_bool_1"), register_term);
        track_registered_term("unconstrained-bool", "free_bool_2", ctx.bool_const("free_bool_2"), register_term);
        track_registered_term("unconstrained-bool", "P(free_int_0)", pred(ctx.int_const("free_int_0")), register_term);
        track_registered_term("unconstrained-bool", "P(free_int_1)", pred(ctx.int_const("free_int_1")), register_term);
        track_registered_term("unconstrained-bool", "P(free_int_2)", pred(ctx.int_const("free_int_2")), register_term);
    }

    template <typename RegisterFn>
    void register_bool_equivalence_terms(const std::string &experiment,
                                         const std::vector<z3::expr> &terms,
                                         RegisterFn &&register_term)
    {
        for (const auto &term : terms)
            track_registered_term(experiment, term.to_string(), term, register_term);

        for (std::size_t i = 0; i < terms.size(); ++i)
            for (std::size_t j = i + 1; j < terms.size(); ++j)
                watch_pair("eq(" + terms[i].to_string() + ", " + terms[j].to_string() + ")",
                           terms[i],
                           terms[j]);
    }

public:
    EqExperimentTracker(Logger &log, bool emit_summary)
        : log_(&log), emit_summary_(emit_summary)
    {
    }

    template <typename RegisterFn>
    void register_configured_terms(z3::context &ctx,
                                   const std::vector<z3::expr> &eqps,
                                   const EqExperimentOptions &options,
                                   RegisterFn &&register_term)
    {
        if (!options.enabled())
            return;

        if (options.ntt_red_mul)
            register_ntt_red_mul(ctx, eqps, register_term);
        if (options.bv_indirect)
            register_bv_indirect(ctx, register_term);
        if (options.bool_indirect)
            register_bool_indirect(ctx, register_term);
        if (options.bool_indirect_3)
            register_bool_indirect_3(ctx, register_term);
        if (options.bool_indirect_4)
            register_bool_indirect_4(ctx, register_term);
        if (options.unconstrained_bool)
            register_unconstrained_bool(ctx, register_term);
    }

    void on_fixed(const z3::expr &t, const z3::expr &v)
    {
        auto it = term_index_.find((Z3_ast)t);
        if (it == term_index_.end())
            return;

        ObservedTerm &row = terms_[it->second];
        const std::string value = v.to_string();
        if (row.fixed_seen && row.fixed_value == value)
            return;

        row.fixed_seen = true;
        row.fixed_value = value;
        LOG_INFO(*log_, "eqexp",
                 "fixed observed: " + row.experiment +
                     " :: " + row.display_name +
                     " :: value=" + value +
                     " :: bv_width=" + (row.bv_width == 0 ? std::string("-") : std::to_string(row.bv_width)));
    }

    template <typename IsRegisteredFn, typename FormatFixedFn>
    void on_eq(const z3::expr &x,
               const z3::expr &y,
               IsRegisteredFn &&is_registered,
               FormatFixedFn &&format_fixed_value)
    {
        ++eq_event_count_;
        note_eq_arg(x);
        note_eq_arg(y);
        mark_eq_pair_if_watched(x, y);

        const bool x_registered = is_registered(x);
        const bool y_registered = is_registered(y);
        if (!(x_registered && y_registered))
        {
            ++eq_event_with_unregistered_arg_count_;
            if (eq_event_samples_with_unregistered_args_.size() < 8)
                eq_event_samples_with_unregistered_args_.push_back(x.to_string() + " == " + y.to_string());
        }

        LOG_TRACE(*log_, "eqexp",
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
        oss << "===== [eq experiment summary] =====\n";
        oss << "Experiment | Term | Registered | Fixed | Fixed Value | Seen In eq() | BV Width\n";
        for (const auto &row : terms_)
        {
            oss << row.experiment << " | "
                << row.display_name << " | "
                << yes_no(row.registered) << " | "
                << yes_no(row.fixed_seen) << " | "
                << row.fixed_value << " | "
                << yes_no(row.seen_in_eq) << " | ";
            if (row.bv_width == 0)
                oss << "-";
            else
                oss << row.bv_width;
            oss << "\n";
        }
        for (const auto &pair : watched_pairs_)
            oss << "Observed " << pair.label << ": " << yes_no(pair.observed) << "\n";
        oss << "Total eq() events: " << eq_event_count_ << "\n";
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
        LOG_INFO(*log_, "eqexp", "\n" + summary);
    }
};

} // namespace util
