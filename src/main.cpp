#include <z3++.h>
#include <z3.h>
#include <Singular/libsingular.h>
#include <gmpxx.h>
#include <limits>
#include <gmp.h>
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <cctype>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <stdexcept>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include <sstream>
#include <functional>

#include "cli_options.hpp"
#include "cli_report.hpp"
#include "eqmod_engine.hpp"
#include "smt2_frontend.hpp"
#include "solver_option_adapters.hpp"
#include "util/auto_zero_lemmas.hpp"
#include "util/eqmod_slots.hpp"
#include "util/fmt_duration.hpp"
#include "util/bv_eq.hpp"
#include "util/eq_callback.hpp"
#include "util/implied_eq_partition_prepass.hpp"
#include "util/implied_eq_partition_refiner.hpp"
#include "util/live_global_eq_validator.hpp"
#include "util/logger.hpp"
#include "util/rewrite.hpp"
#include "util/singular_dump.hpp"
#include "util/singular_capacity.hpp"
#include "util/singular_lift_prover.hpp"
#include "util/singular_lowering.hpp"
#include "util/singular_membership_prover.hpp"
#include "util/singular_process_pool.hpp"
#include "util/singular_runtime_stats.hpp"

using namespace z3;
using namespace util::singular::lowering;
using util::singular::copy_poly_or_null;
using util::singular::delete_poly_if_nonnull;
using util::singular::num_from_si;
using util::singular::poly_add_owned;
using util::singular::poly_equal;
using util::singular::poly_from_mpz;
using util::singular::poly_from_si;
using util::singular::poly_mul_clone;
using util::singular::poly_negate_owned;
using util::singular::poly_sub_product_clone;
using util::singular::poly_to_string;
using util::singular::ScopedPolyOwner;
using util::singular::ScopedPolyVectorOwner;
using clk = std::chrono::steady_clock;

static bool SHOW_MODEL = true;
static bool PRINT_PROPAGATE = true;
static util::Logger g_log;
static cli::Options g_cli;

static bool eq_gb_generator_mode_enabled()
{
    return g_cli.enable_eq_gb_live;
}

static bool eq_gb_live_heuristic_enabled()
{
    // The pure partition-refinement mode deliberately disables every live
    // candidate source and validator. The hybrid mode, and the original
    // --enable-eq-gb-live mode by itself, retain the live heuristic.
    return g_cli.enable_eq_gb_live &&
           !g_cli.eq_gb_live_partition_refinement;
}

static bool eq_gb_partition_refinement_enabled()
{
    return g_cli.eq_gb_live_hybrid ||
           g_cli.eq_gb_live_partition_refinement;
}

static bool rewrite_aware_coeff_views_enabled()
{
    return g_cli.enable_eq_gb_live;
}

static cli::report::AccumulatedTiming g_groebner_timing;
static cli::report::AccumulatedTiming g_final_fixed_value_check_timing;
static std::optional<clk::time_point> g_final_fixed_value_check_span_start;

static void init_singular()
{
    (void)singular_shared_coeffs_Z();
}

static void dump_ring(const ring R)
{
    if (!g_cli.ring_detail)
        return;

    LOG_INFO(g_log, "singular", "Current ring:");
    rWrite(R);
    std::cout << "\n";
}

// ---------------- helpers ----------------
static bool is_tracking_symbol_name(const std::string &name)
{
    if (name.size() < 3)
        return false;
    if (name[0] != 'A' || name[1] != '#')
        return false;
    for (size_t i = 2; i < name.size(); ++i)
    {
        if (!std::isdigit((unsigned char)name[i]))
            return false;
    }
    return true;
}

static void print_model_filtered(const z3::model &m, std::ostream &os = std::cout)
{
    os << "Model:\n";

    Z3_context c = (Z3_context)m.ctx();
    Z3_model zm = (Z3_model)m;

    for (unsigned i = 0; i < m.size(); ++i)
    {
        z3::func_decl fd = m[i];
        std::string name = fd.name().str();

        if (is_tracking_symbol_name(name))
            continue;

        if (fd.arity() != 0)
            continue;

        Z3_func_decl zfd = (Z3_func_decl)fd;
        Z3_ast ast = Z3_model_get_const_interp(c, zm, zfd);
        if (ast == nullptr)
            continue;

        z3::expr val(m.ctx(), ast);

        os << "(define-fun " << name
           << " () " << fd.range()
           << "\n  " << val
           << ")\n";
    }
}

static std::string sanitize_ring_var_base(const std::string &s)
{
    std::string r;
    r.reserve(s.size());
    for (char ch : s)
    {
        if (std::isalnum((unsigned char)ch) || ch == '_')
            r.push_back(ch);
        else
            r.push_back('_');
    }
    if (r.empty() || std::isdigit((unsigned char)r[0]))
        r = "v_" + r;
    return r;
}

static std::string make_unique_name(const std::string &base, std::unordered_set<std::string> &used)
{
    if (!used.count(base))
    {
        used.insert(base);
        return base;
    }
    for (int k = 1;; ++k)
    {
        std::string cand = base + "_u" + std::to_string(k);
        if (!used.count(cand))
        {
            used.insert(cand);
            return cand;
        }
    }
}

static bool starts_with(const std::string &s, const char *prefix)
{
    const std::size_t n = std::strlen(prefix);
    return s.size() >= n && s.compare(0, n, prefix) == 0;
}

static bool is_groebner_aux_var(const std::string &name)
{
    return starts_with(name, "tmp") || starts_with(name, "mulH");
}

static std::vector<std::string> build_groebner_ring_var_order(
    const std::vector<std::string> &coeff_ring_names,
    const std::vector<std::string> &poly_symbol_ring_names,
    const std::vector<std::string> &indet_ring_names,
    const std::vector<std::string> &qvar_names,
    const std::vector<std::vector<std::vector<std::string>>> &eqmodn_qvar_names)
{
    std::vector<std::string> aux;
    std::vector<std::string> coeffs;
    aux.reserve(coeff_ring_names.size());
    coeffs.reserve(coeff_ring_names.size());

    for (const auto &name : coeff_ring_names)
    {
        if (is_groebner_aux_var(name))
            aux.push_back(name);
        else
            coeffs.push_back(name);
    }

    auto descending = [](std::vector<std::string> &xs)
    {
        std::sort(xs.begin(), xs.end(), std::greater<std::string>());
    };
    descending(aux);
    descending(coeffs);

    std::vector<std::string> ring_vars;
    ring_vars.reserve(coeff_ring_names.size() + poly_symbol_ring_names.size() + indet_ring_names.size() +
                      qvar_names.size());

    // P4, P3, P2 in reverse atom order, followed by the specialized P1 slots.
    for (unsigned arity = 4; arity >= 2; --arity)
    {
        const auto &family = eqmodn_qvar_names.at(arity);
        for (auto atom = family.rbegin(); atom != family.rend(); ++atom)
            ring_vars.insert(ring_vars.end(), atom->begin(), atom->end());
    }
    for (auto it = qvar_names.rbegin(); it != qvar_names.rend(); ++it)
        ring_vars.push_back(*it);

    // Opaque polynomial symbols precede every variable that can occur in
    // their defining relation, so p^k - F is oriented by p^k in lp order.
    ring_vars.insert(ring_vars.end(), poly_symbol_ring_names.begin(), poly_symbol_ring_names.end());
    ring_vars.insert(ring_vars.end(), aux.begin(), aux.end());
    ring_vars.insert(ring_vars.end(), coeffs.begin(), coeffs.end());
    ring_vars.insert(ring_vars.end(), indet_ring_names.begin(), indet_ring_names.end());
    return ring_vars;
}

static std::vector<expr> dedup_and_drop_trivial_eqp(const std::vector<expr> &eqps)
{
    std::vector<expr> out;
    out.reserve(eqps.size());
    std::unordered_set<std::string> seen;
    for (const auto &e : eqps)
    {
        if (!(e.is_app() && e.decl().name().str() == "eqP" && e.num_args() == 2))
            continue;
        if ((e.arg(0) == e.arg(1)).simplify().is_true())
            continue;
        if (seen.insert(e.to_string()).second)
            out.push_back(e);
    }
    return out;
}

// ---------------- collectors (used after rewriting for Singular lowering) -------------
static void collect_eqP_rec(const expr &e, std::vector<expr> &atoms)
{
    if (!e.is_app())
        return;
    if (e.decl().name().str() == "eqP" && e.num_args() == 2)
    {
        atoms.push_back(e);
        return;
    }
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_eqP_rec(e.arg(i), atoms);
}

static void collect_eqmod_rec(const expr &e,
                              unsigned arity,
                              std::vector<expr> &atoms,
                              std::unordered_set<Z3_ast> &seen)
{
    if (!e.is_app())
        return;
    const std::string expected = "eqmodP" + std::to_string(arity);
    if (e.decl().name().str() == expected && e.num_args() == arity + 2)
    {
        if (seen.insert((Z3_ast)e).second)
            atoms.push_back(e);
        return;
    }
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_eqmod_rec(e.arg(i), arity, atoms, seen);
}

static void collect_eqmod_rec(const expr &e, unsigned arity, std::vector<expr> &atoms)
{
    std::unordered_set<Z3_ast> seen;
    seen.reserve(atoms.size() + 1);
    for (const expr &atom : atoms)
        seen.insert((Z3_ast)atom);
    collect_eqmod_rec(e, arity, atoms, seen);
}

// ---------------- eqP compilation ----------------
struct EqPCompiled
{
    expr atom;
    expr A;
    expr B;

    std::vector<expr> coeff_ints;
    std::vector<expr> coeff_eqs;
    expr coeff_neq_disj;
    bool relational = false;
    bool always_equal = false;

    poly D_full = nullptr; // owned
};

static EqPCompiled compile_eqP_singular(const expr &atom, const expr &A, const expr &B,
                                        const std::string &label,
                                        const IndetEnv &env,
                                        const std::vector<std::string> &indet_ring_names,
                                        RingEnv &RE,
                                        const CoeffVarMap &cmap,
                                        int Nc, int Mi)
{
    context &zctx = atom.ctx();
    ring R = RE.R;
    rChangeCurrRing(R);

    EqPCompiled out{atom, A, B, {}, {}, zctx.bool_val(false),
                    contains_raw_poly_symbol(A) || contains_raw_poly_symbol(B),
                    false, nullptr};

    poly pA = polyterm_to_singular_poly(A, env, indet_ring_names, RE, cmap, Nc, label + "/LHS");
    poly pB = polyterm_to_singular_poly(B, env, indet_ring_names, RE, cmap, Nc, label + "/RHS");

    LOG_TRACE(g_log, "singular", label + " LHS(poly) = " + poly_to_string(pA, R));
    LOG_TRACE(g_log, "singular", label + " RHS(poly) = " + poly_to_string(pB, R));

    number m1 = num_from_si(-1, R->cf);
    poly pBn = p_Mult_nn(pB, m1, R);
    n_Delete(&m1, R->cf);
    poly D = p_Add_q(pA, pBn, R);

    if (D == nullptr)
    {
        out.always_equal = true;
        out.coeff_neq_disj = zctx.bool_val(false);
        out.D_full = nullptr;
        return out;
    }

    out.D_full = p_Copy(D, R);

    if (out.relational)
    {
        // D=0 is retained as one algebraic relation.  Splitting by PVar
        // monomials would incorrectly treat the opaque polynomial symbol as
        // an expanded coefficient polynomial and can manufacture 1=0.
        p_Delete(&D, R);
        return out;
    }

    auto groups = split_by_indets(D, cmap, Mi, RE);
    if (D)
        p_Delete(&D, R);

    expr disj = zctx.bool_val(false);

    for (auto &kv : groups)
    {
        poly coeffP = kv.second;

        expr coeffE = coeff_poly_to_z3_expr(zctx, coeffP, R, cmap);
        out.coeff_ints.push_back(coeffE);

        expr eq0 = (coeffE == zctx.int_val(0)).simplify();
        if (!eq0.is_true())
            out.coeff_eqs.push_back(eq0);

        expr ne0 = (coeffE != zctx.int_val(0)).simplify();
        if (ne0.is_true())
            disj = zctx.bool_val(true);
        else if (!ne0.is_false() && !disj.is_true())
            disj = (disj || ne0).simplify();

        if (coeffP)
            p_Delete(&coeffP, R);
    }

    out.coeff_neq_disj = disj.simplify();
    return out;
}

using eqmod::make_var_poly;

// -------------------------- Propagator --------------------------

class PolyPropagator : public user_propagator_base, protected eqmod::EqmodEngine
{
    struct EqFact
    {
        expr lhs;
        expr rhs;
        Z3_ast first_key = nullptr;
        Z3_ast second_key = nullptr;
        std::size_t generator_count = 0;
        bool globally_proved = false;
    };

    IndetEnv m_env;
    CoeffVarMap m_cmap;

    std::vector<std::string> m_indet_ring_names;
    std::vector<std::string> m_ring_vars;

    int m_Nc = 0;
    int m_Mi = 0;

    std::vector<EqPCompiled> m_eqp;

    std::unordered_map<Z3_ast, Z3_lbool> m_bool_cache;
    std::unordered_map<Z3_ast, Z3_ast> m_fixed_ast_cache;

    RingEnv m_RE;

    std::unordered_map<Z3_ast, std::string> m_label;
    std::unordered_set<Z3_ast> m_registered_terms;
    util::EqCallbackOptions m_eq_callback_options;
    util::EqCallbackTracker m_eq_callback_tracker;
    std::vector<expr> m_all_bv_terms;
    std::vector<RewrittenCoeffBase> m_eq_coeff_views;
    std::vector<expr> m_online_bv_constraints;
    std::vector<expr> m_online_bv_terms;
    std::vector<std::pair<expr, expr>> m_partition_prepass_equalities;
    std::vector<expr> m_partition_prepass_triggers;
    bool m_partition_prepass_propagated = false;
    std::size_t m_partition_prepass_propagation_requested = 0;
    std::size_t m_partition_prepass_propagation_accepted = 0;
    bool m_allow_live_validator = true;
    // Declared before the threaded validator so reverse member destruction
    // joins validator threads before stopping the Singular worker processes.
    std::unique_ptr<util::singular::MembershipProcessPool> m_gb_process_pool;
    std::unique_ptr<util::eqpartition::ImpliedEqualityPartitionRefiner>
        m_eq_partition_refiner;
    std::unique_ptr<util::eqgb::LiveGlobalEqValidator> m_live_eq_validator;
    std::vector<expr> m_live_eq_terms;
    std::unordered_map<Z3_ast, std::size_t> m_live_eq_term_indices;
    std::unordered_set<std::uint64_t> m_live_eq_applied_keys;
    // Main-side compact dedup keeps repeated scoped closure construction away
    // from the validator mutex.  A direct observation may still promote a
    // pair that was first seen through closure, so it has its own seen set.
    std::unordered_set<std::uint64_t> m_live_eq_pair_attempted_keys;
    std::unordered_set<std::uint64_t> m_live_eq_direct_attempted_keys;
    std::size_t m_live_eq_applied = 0;
    std::size_t m_live_eq_applied_during_search = 0;
    std::size_t m_live_eq_applied_at_final = 0;
    std::size_t m_live_eq_direct_seen = 0;
    std::size_t m_live_eq_callback_submitted = 0;
    std::size_t m_live_eq_closure_seen = 0;
    std::size_t m_live_eq_closure_submitted = 0;
    bool m_live_eq_in_final = false;
    std::size_t m_live_eq_propagated = 0;
    std::size_t m_conflict_generation = 0;
    std::size_t m_live_eq_empty_drains_avoided = 0;
    std::size_t m_live_eq_final_waits = 0;
    std::size_t m_live_eq_final_waves = 0;
    std::chrono::nanoseconds m_live_eq_final_wait_time{0};
    struct LiveEqUnionUndo
    {
        std::size_t child = 0;
        std::size_t parent = 0;
        std::size_t old_parent_size = 0;
        std::size_t old_parent_members = 0;
    };
    std::vector<std::size_t> m_live_eq_union_parent;
    std::vector<std::size_t> m_live_eq_union_size;
    std::vector<std::vector<std::size_t>> m_live_eq_union_members;
    std::vector<LiveEqUnionUndo> m_live_eq_union_trail;
    std::vector<std::pair<expr, expr>> m_proved_global_eq;
    // Equality lemmas are useful to Z3 as soon as validation finishes, but
    // inserting them into the Singular ideal one at a time invalidates every
    // pending membership check.  Commit them to the GB forest in coarse
    // batches while still propagating each proved equality immediately.
    static constexpr std::size_t LIVE_EQ_GB_BATCH_SIZE = 128;
    std::size_t m_live_eq_gb_committed = 0;
    std::size_t m_live_eq_gb_flushes = 0;
    std::size_t m_live_eq_gb_pending_high_water = 0;
    bool m_eq_partition_results_applied = false;
    std::vector<EqFact> m_eq_facts;
    std::unordered_set<std::string> m_active_eq_keys;
    std::unordered_map<Z3_ast, std::vector<std::size_t>> m_bv_to_eq_view_indices;
    std::size_t m_eq_generator_count = 0;
    struct EqUnionUndo
    {
        std::size_t child = 0;
        std::size_t parent = 0;
        std::size_t old_parent_size = 0;
    };
    std::vector<std::size_t> m_eq_union_parent;
    std::vector<std::size_t> m_eq_union_size;
    std::vector<EqUnionUndo> m_eq_union_trail;
    // Version of the equality-derived generator set, not of every observed
    // equality callback.  GB caches only depend on equalities that can
    // actually be translated into the current Singular ring.
    std::size_t m_eq_generator_epoch = 0;

    bool m_minimal_eval_watch_registered = false;
    std::unordered_set<Z3_ast> m_eval_watch_registered;

    struct BoolTrailEntry
    {
        Z3_ast key = nullptr;
        bool had_old = false;
        Z3_lbool old_value = Z3_L_UNDEF;
    };

    struct FixedAstTrailEntry
    {
        Z3_ast key = nullptr;
        bool had_old = false;
        Z3_ast old_value = nullptr;
    };

    struct TrailMark
    {
        size_t bool_size = 0;
        size_t fixed_ast_size = 0;
        size_t eq_size = 0;
        size_t eq_union_size = 0;
        size_t live_eq_union_size = 0;
    };

    std::vector<BoolTrailEntry> m_bool_trail;
    std::vector<FixedAstTrailEntry> m_fixed_ast_trail;
    std::vector<TrailMark> m_trail_marks;

    // --- search progress tracking ---
    using search_clk = std::chrono::steady_clock;
    search_clk::time_point m_search_start = search_clk::now();
    std::size_t m_search_push_count = 0;
    std::size_t m_search_pop_count = 0;
    std::size_t m_search_fixed_count = 0;
    std::size_t m_search_fixed_bool_count = 0;
    std::size_t m_search_eq_count = 0;
    std::size_t m_search_created_count = 0;
    std::size_t m_search_final_count = 0;
    std::size_t m_search_max_depth = 0;
    search_clk::time_point m_search_last_progress = search_clk::now();
    static constexpr double SEARCH_PROGRESS_INTERVAL_SEC = 5.0;

    bool enable_all_true() const override { return g_cli.enable_all_true; }
    bool enable_all_false() const override { return g_cli.enable_all_false; }
    bool enable_mixed() const override { return g_cli.enable_mixed; }
    bool assume_p1_modulus_prime() const override
    {
        return g_cli.all_false_assume_m_prime;
    }
    bool reuse_base_basis() const override
    {
        return g_cli.eq_gb_reuse_base_basis;
    }
    bool preprocess_membership() const override
    {
        return g_cli.enable_gb_preprocess;
    }
    bool verify_membership_preprocess() const override
    {
        return g_cli.verify_gb_preprocess;
    }
    bool enable_ideal_rewrite() const override
    {
        return g_cli.enable_ideal_rewrite;
    }
    bool enable_true_lemmas() const override
    {
        return g_cli.enable_eqmod_true_lemmas;
    }
    bool enable_true_lemma_lift_antecedents() const override
    {
        return g_cli.enable_eqmod_true_lemma_lift_antecedents;
    }
    bool enable_true_lemma_cache() const override
    {
        return g_cli.enable_eq_gb_live;
    }
    std::size_t refutation_processes() const override
    {
        return g_cli.eq_gb_refutation_processes;
    }
    std::size_t true_lemma_processes() const override
    {
        return g_cli.eq_gb_true_lemma_processes;
    }
    util::Logger &engine_log() override { return g_log; }
    ring engine_ring() const override { return m_RE.R; }
    void accumulate_direct_membership_timing(
        const util::singular::GroebnerTiming &timing) override
    {
        g_groebner_timing.calls += timing.calls;
        g_groebner_timing.elapsed += timing.elapsed;
    }

    void search_progress_tick(const char *event)
    {
        auto now = search_clk::now();
        double elapsed_since_last =
            std::chrono::duration<double>(now - m_search_last_progress).count();
        if (elapsed_since_last < SEARCH_PROGRESS_INTERVAL_SEC)
            return;
        m_search_last_progress = now;
        LOG_INFO(g_log, "search",
                 "[progress " + util::fmt_duration(now - m_search_start) + "] "
                 "event=" + std::string(event) +
                 " depth=" + std::to_string(m_trail_marks.size()) +
                 " max_depth=" + std::to_string(m_search_max_depth) +
                 " push=" + std::to_string(m_search_push_count) +
                 " pop=" + std::to_string(m_search_pop_count) +
                 " fixed=" + std::to_string(m_search_fixed_count) +
                 " fixed_bool=" + std::to_string(m_search_fixed_bool_count) +
                 " eq=" + std::to_string(m_search_eq_count) +
                 " created=" + std::to_string(m_search_created_count) +
                 " final=" + std::to_string(m_search_final_count));
    }

    std::string label_of(const expr &e) const override
    {
        auto it = m_label.find((Z3_ast)e);
        if (it != m_label.end())
            return it->second;
        return e.to_string();
    }

    std::string format_fixed_value_for_log(const expr &t) const
    {
        expr v = t;
        if (!try_get_fixed_expr(t, v))
            return "<not-fixed>";
        return v.to_string();
    }

    bool is_registered_term(const expr &e) const
    {
        return m_registered_terms.count((Z3_ast)e) != 0;
    }

    void tracked_add(const expr &e)
    {
        if (!m_registered_terms.insert((Z3_ast)e).second)
            return;
        this->add(e);
    }

    bool is_partition_prepass_trigger(const expr &term) const
    {
        return !m_partition_prepass_triggers.empty() &&
               z3::eq(term, m_partition_prepass_triggers.front());
    }

    void propagate_partition_prepass_equalities(const expr &trigger,
                                                const expr &value)
    {
        if (m_partition_prepass_propagated ||
            m_partition_prepass_equalities.empty() ||
            !is_partition_prepass_trigger(trigger))
            return;

        if (!value.is_true())
            throw std::runtime_error(
                "partition prepass propagation trigger was not fixed true");

        // Mark the one-shot before enqueuing consequences.  Z3 may process
        // callbacks triggered by these propagations before this callback has
        // completely unwound.
        m_partition_prepass_propagated = true;
        expr_vector fixed_premises(ctx());
        fixed_premises.push_back(trigger);
        m_partition_prepass_propagation_requested =
            m_partition_prepass_equalities.size();
        for (const auto &[lhs, rhs] : m_partition_prepass_equalities)
        {
            if (this->propagate(fixed_premises, lhs == rhs))
                ++m_partition_prepass_propagation_accepted;
        }

        LOG_INFO(g_log, "eqpartition",
                 "partition prepass search-start propagation: requested=" +
                     std::to_string(m_partition_prepass_propagation_requested) +
                     " accepted=" +
                     std::to_string(m_partition_prepass_propagation_accepted) +
                     " fixed-callback=" +
                     std::to_string(m_search_fixed_count) +
                     " depth=" + std::to_string(m_trail_marks.size()));
    }

    bool eq_trace_enabled() const
    {
        return m_eq_callback_tracker.trace_enabled(m_eq_callback_options);
    }

    bool eq_fact_tracking_enabled() const
    {
        return eq_trace_enabled() || eq_gb_generator_mode_enabled();
    }

    static std::pair<Z3_ast, Z3_ast> canonical_eq_keys(const expr &x, const expr &y)
    {
        Z3_ast xa = (Z3_ast)x;
        Z3_ast ya = (Z3_ast)y;
        const unsigned xid = Z3_get_ast_id((Z3_context)x.ctx(), xa);
        const unsigned yid = Z3_get_ast_id((Z3_context)y.ctx(), ya);
        return xid <= yid ? std::make_pair(xa, ya) : std::make_pair(ya, xa);
    }

    std::string eq_key(Z3_ast first, Z3_ast second) const
    {
        std::ostringstream oss;
        oss << first << ':' << second;
        return oss.str();
    }

    bool compatible_eq_views(std::size_t lhs_idx, std::size_t rhs_idx) const
    {
        const expr &lhs_base = m_eq_coeff_views[lhs_idx].original_base;
        const expr &rhs_base = m_eq_coeff_views[rhs_idx].original_base;
        if (!is_bv_to_int_app(lhs_base) || !is_bv_to_int_app(rhs_base))
            return false;
        const expr lhs_bv = lhs_base.arg(0);
        const expr rhs_bv = rhs_base.arg(0);
        return lhs_bv.get_sort().bv_size() == rhs_bv.get_sort().bv_size() &&
               Z3_is_eq_func_decl((Z3_context)lhs_base.ctx(),
                                  (Z3_func_decl)lhs_base.decl(),
                                  (Z3_func_decl)rhs_base.decl());
    }

    bool has_compatible_eq_views(const expr &x, const expr &y) const
    {
        auto xi = m_bv_to_eq_view_indices.find((Z3_ast)x);
        auto yi = m_bv_to_eq_view_indices.find((Z3_ast)y);
        if (xi == m_bv_to_eq_view_indices.end() || yi == m_bv_to_eq_view_indices.end())
            return false;
        for (std::size_t lhs_idx : xi->second)
            for (std::size_t rhs_idx : yi->second)
                if (lhs_idx != rhs_idx && compatible_eq_views(lhs_idx, rhs_idx))
                    return true;
        return false;
    }

    void initialize_live_eq_validator()
    {
        if (!g_cli.enable_eq_gb_live || !m_allow_live_validator)
            return;

        std::unordered_set<Z3_ast> seen;
        for (const expr &term : m_online_bv_terms)
            if (m_bv_to_eq_view_indices.count((Z3_ast)term) != 0 &&
                seen.insert((Z3_ast)term).second)
                m_live_eq_terms.push_back(term);
        std::sort(m_live_eq_terms.begin(), m_live_eq_terms.end(),
                  [](const expr &lhs, const expr &rhs) {
                      return lhs.to_string() < rhs.to_string();
                  });
        for (std::size_t i = 0; i < m_live_eq_terms.size(); ++i)
            m_live_eq_term_indices.emplace((Z3_ast)m_live_eq_terms[i], i);
        m_live_eq_union_parent.resize(m_live_eq_terms.size());
        std::iota(m_live_eq_union_parent.begin(), m_live_eq_union_parent.end(), 0);
        m_live_eq_union_size.assign(m_live_eq_terms.size(), 1);
        m_live_eq_union_members.resize(m_live_eq_terms.size());
        for (std::size_t i = 0; i < m_live_eq_terms.size(); ++i)
            m_live_eq_union_members[i].push_back(i);
        m_live_eq_union_trail.clear();

        const char *discovery_mode =
            g_cli.eq_gb_live_partition_refinement
                ? "partition-refinement-pure"
                : (g_cli.eq_gb_live_hybrid ? "hybrid" : "live-heuristic");
        LOG_INFO(g_log, "eqgb",
                 std::string("equality discovery mode=") + discovery_mode +
                     " terms=" + std::to_string(m_live_eq_terms.size()) +
                     " live-validator=" +
                     (eq_gb_live_heuristic_enabled() ? "on" : "off") +
                     " complete-partition=" +
                     (eq_gb_partition_refinement_enabled() ? "on" : "off"));

        if (eq_gb_partition_refinement_enabled())
        {
            util::eqpartition::Options options;
            options.timeout_ms = 0;
            // The complete refiner is intentionally run at the final barrier.
            // Running another full-formula solver concurrently with the Main
            // Solver causes severe memory-bandwidth contention on large BV
            // inputs and obscures the cost comparison.
            options.start_async = false;
            m_eq_partition_refiner = std::make_unique<
                util::eqpartition::ImpliedEqualityPartitionRefiner>(
                ctx(), m_online_bv_constraints, m_live_eq_terms,
                options, &g_log);
        }

        if (eq_gb_live_heuristic_enabled())
        {
            util::eqgb::LiveValidatorOptions options;
            options.workers = g_cli.eq_gb_live_workers;
            options.seed_models = g_cli.eq_gb_live_seed_models;
            options.unified_queue = g_cli.eq_gb_live_unified_queue;
            m_live_eq_validator =
                std::make_unique<util::eqgb::LiveGlobalEqValidator>(
                    ctx(), m_online_bv_constraints, m_live_eq_terms,
                    options, &g_log);
        }
    }

    void initialize_gb_process_pool()
    {
        if (!m_allow_live_validator || m_RE.R == nullptr)
            return;
        const std::size_t workers = std::max(
            g_cli.eq_gb_true_lemma_processes,
            g_cli.eq_gb_refutation_processes);
        if (workers == 0)
            return;
        // This runs before initialize_live_eq_validator(), hence before any
        // application worker threads exist. Never fork lazily during search.
        m_gb_process_pool =
            std::make_unique<util::singular::MembershipProcessPool>(
                m_RE.R, workers, &g_log);
    }

    util::singular::MembershipGroupBatchResult run_membership_groups(
        const std::vector<poly> &base,
        const std::vector<util::singular::MembershipGroup> &groups,
        std::size_t processes,
        bool return_normal_forms) override
    {
        ++m_eqmod_membership_batch_calls;
        m_eqmod_membership_batch_groups += groups.size();
        for (const auto &group : groups)
            m_eqmod_membership_batch_targets += group.targets.size();
        util::singular::MembershipGroupBatchOptions options;
        options.membership.preprocess = g_cli.enable_gb_preprocess;
        options.membership.verify_preprocess = g_cli.verify_gb_preprocess;
        options.membership.ideal_rewrite =
            g_cli.enable_ideal_rewrite;
        options.reuse_base_basis = g_cli.eq_gb_reuse_base_basis;
        options.return_normal_forms = return_normal_forms;
        options.processes = processes;
        if (processes != 0)
        {
            if (m_gb_process_pool)
                return m_gb_process_pool->run(base, groups, options);
            // Z3 may request a translated propagator after application
            // threads exist. Never fork lazily there; preserve serial soundness.
            options.processes = 0;
        }
        return util::singular::prove_membership_groups_serial(
            base, groups, m_RE.R, options, &g_log);
    }

    void accumulate_membership_group_timing(
        const util::singular::MembershipGroupBatchResult &batch) override
    {
        g_groebner_timing.calls += batch.base_groebner.calls;
        g_groebner_timing.elapsed += batch.base_groebner.elapsed;
        for (const auto &group : batch.groups)
        {
            g_groebner_timing.calls += group.groebner.calls;
            g_groebner_timing.elapsed += group.groebner.elapsed;
        }
    }

    bool live_eq_is_applied(const expr &lhs, const expr &rhs) const
    {
        auto lhs_index = m_live_eq_term_indices.find((Z3_ast)lhs);
        auto rhs_index = m_live_eq_term_indices.find((Z3_ast)rhs);
        if (lhs_index == m_live_eq_term_indices.end() ||
            rhs_index == m_live_eq_term_indices.end())
            return false;
        return m_live_eq_applied_keys.count(
                   live_eq_pair_key(lhs_index->second, rhs_index->second)) != 0;
    }

    std::size_t live_eq_union_root(std::size_t node) const
    {
        while (m_live_eq_union_parent[node] != node)
            node = m_live_eq_union_parent[node];
        return node;
    }

    void live_eq_union_components(std::size_t lhs, std::size_t rhs)
    {
        lhs = live_eq_union_root(lhs);
        rhs = live_eq_union_root(rhs);
        if (lhs == rhs)
            return;
        if (m_live_eq_union_size[lhs] < m_live_eq_union_size[rhs])
            std::swap(lhs, rhs);
        m_live_eq_union_trail.push_back(
            {rhs, lhs, m_live_eq_union_size[lhs],
             m_live_eq_union_members[lhs].size()});
        m_live_eq_union_parent[rhs] = lhs;
        m_live_eq_union_size[lhs] += m_live_eq_union_size[rhs];
        m_live_eq_union_members[lhs].insert(
            m_live_eq_union_members[lhs].end(),
            m_live_eq_union_members[rhs].begin(),
            m_live_eq_union_members[rhs].end());
    }

    void rollback_live_eq_union(std::size_t size)
    {
        while (m_live_eq_union_trail.size() > size)
        {
            const LiveEqUnionUndo undo = m_live_eq_union_trail.back();
            m_live_eq_union_trail.pop_back();
            m_live_eq_union_parent[undo.child] = undo.child;
            m_live_eq_union_size[undo.parent] = undo.old_parent_size;
            m_live_eq_union_members[undo.parent].resize(undo.old_parent_members);
        }
    }

    bool submit_live_eq_pair(std::size_t lhs_index, std::size_t rhs_index,
                             bool direct)
    {
        if (lhs_index == rhs_index || !m_live_eq_validator ||
            lhs_index >= m_live_eq_terms.size() ||
            rhs_index >= m_live_eq_terms.size())
            return false;
        const std::uint64_t key = live_eq_pair_key(lhs_index, rhs_index);
        if (direct)
        {
            ++m_live_eq_direct_seen;
            if (!m_live_eq_direct_attempted_keys.insert(key).second)
            {
                // Repeated direct observations carry useful ranking data even
                // though the pair itself is already deduplicated.
                m_live_eq_validator->submit_direct_candidate(
                    lhs_index, rhs_index, m_trail_marks.size());
                return false;
            }
            // Preserve one direct promotion attempt even if closure submitted
            // this pair first.
            m_live_eq_pair_attempted_keys.insert(key);
        }
        else
        {
            ++m_live_eq_closure_seen;
            if (!m_live_eq_pair_attempted_keys.insert(key).second)
                return false;
        }
        const expr &lhs = m_live_eq_terms[lhs_index];
        const expr &rhs = m_live_eq_terms[rhs_index];
        if (!has_compatible_eq_views(lhs, rhs))
            return false;
        const bool accepted = direct
                                  ? m_live_eq_validator->submit_direct_candidate(
                                        lhs_index, rhs_index,
                                        m_trail_marks.size())
                                  : m_live_eq_validator->submit_derived_candidate(
                                        lhs_index, rhs_index,
                                        m_trail_marks.size());
        if (!accepted)
            return false;
        if (direct)
            ++m_live_eq_callback_submitted;
        else
        {
            ++m_live_eq_closure_submitted;
        }
        return true;
    }

    bool submit_live_eq_candidate(const expr &lhs, const expr &rhs)
    {
        if (!m_live_eq_validator)
            return false;
        auto lhs_index = m_live_eq_term_indices.find((Z3_ast)lhs);
        auto rhs_index = m_live_eq_term_indices.find((Z3_ast)rhs);
        if (lhs_index == m_live_eq_term_indices.end() ||
            rhs_index == m_live_eq_term_indices.end())
            return false;

        const std::size_t lhs_root = live_eq_union_root(lhs_index->second);
        const std::size_t rhs_root = live_eq_union_root(rhs_index->second);
        const bool submitted =
            submit_live_eq_pair(lhs_index->second, rhs_index->second, true);
        if (lhs_root == rhs_root)
            return submitted;
        for (std::size_t left : m_live_eq_union_members[lhs_root])
            for (std::size_t right : m_live_eq_union_members[rhs_root])
                if (!((left == lhs_index->second && right == rhs_index->second) ||
                      (left == rhs_index->second && right == lhs_index->second)))
                    submit_live_eq_pair(left, right, false);
        live_eq_union_components(lhs_root, rhs_root);
        return submitted;
    }

    std::size_t drain_live_eq_results(bool wait_for_idle)
    {
        if (!m_live_eq_validator)
            return 0;
        if (wait_for_idle)
            m_live_eq_validator->wait_until_idle();
        else if (!m_live_eq_validator->has_results())
        {
            ++m_live_eq_empty_drains_avoided;
            return 0;
        }

        expr_vector no_fixed(ctx());
        for (const util::eqgb::ValidationResult &result :
             m_live_eq_validator->drain_results())
        {
            if (result.status != util::eqgb::ValidationStatus::Proved ||
                result.lhs >= m_live_eq_terms.size() ||
                result.rhs >= m_live_eq_terms.size())
                continue;
            const expr &lhs = m_live_eq_terms[result.lhs];
            const expr &rhs = m_live_eq_terms[result.rhs];
            const std::uint64_t key = live_eq_pair_key(result.lhs, result.rhs);
            if (!m_live_eq_applied_keys.insert(key).second)
                continue;

            m_proved_global_eq.emplace_back(lhs, rhs);
            if (g_cli.eq_gb_live_propagate)
            {
                this->propagate(no_fixed, lhs == rhs);
                ++m_live_eq_propagated;
            }
            ++m_live_eq_applied;
            if (m_live_eq_in_final)
                ++m_live_eq_applied_at_final;
            else
                ++m_live_eq_applied_during_search;
            LOG_INFO(g_log, "eqgb",
                     "live applied global equality: " +
                         compact_log_text(lhs.to_string()) + " == " +
                         compact_log_text(rhs.to_string()) +
                         " source=" + (result.direct ? "direct" : "closure") +
                         " phase=" +
                         (m_live_eq_in_final ? "final" : "search") +
                         " validation=" + util::fmt_duration(result.elapsed));
        }
        if (g_cli.eq_gb_live_generators)
            m_live_eq_gb_pending_high_water = std::max(
                m_live_eq_gb_pending_high_water,
                m_proved_global_eq.size() - m_live_eq_gb_committed);
        return flush_pending_live_eq_generators(false);
    }

    std::size_t flush_pending_live_eq_generators(bool force)
    {
        if (!g_cli.enable_eq_gb_live || !g_cli.eq_gb_live_generators ||
            m_live_eq_gb_committed >= m_proved_global_eq.size())
            return 0;

        const std::size_t pending =
            m_proved_global_eq.size() - m_live_eq_gb_committed;
        if (!force && pending < LIVE_EQ_GB_BATCH_SIZE)
            return 0;

        const std::size_t begin = m_live_eq_gb_committed;
        const std::size_t end = m_proved_global_eq.size();
        std::size_t added = 0;
        for (std::size_t i = begin; i < end; ++i)
        {
            const auto &[lhs, rhs] = m_proved_global_eq[i];
            added += activate_equality_fact(lhs, rhs, true, false);
        }
        m_live_eq_gb_committed = end;
        ++m_live_eq_gb_flushes;
        if (added != 0)
            ++m_eq_generator_epoch;

        LOG_INFO(g_log, "eqgb",
                 "live GB equality batch: committed=" +
                     std::to_string(end - begin) +
                     " generators=" + std::to_string(added) +
                     " force=" + (force ? "true" : "false") +
                     " total-committed=" + std::to_string(end) +
                     " epoch=" + std::to_string(m_eq_generator_epoch));
        return added;
    }

    std::size_t apply_partition_refinement_results()
    {
        if (!m_eq_partition_refiner || m_eq_partition_results_applied)
            return 0;

        const util::eqpartition::Result &result =
            m_eq_partition_refiner->wait();
        if (result.status != util::eqpartition::Status::Complete)
        {
            throw std::runtime_error(
                "implied-equality partition refinement did not complete: " +
                std::string(util::eqpartition::status_name(result.status)) +
                (result.diagnostic.empty()
                     ? std::string()
                     : std::string(" (") + result.diagnostic + ")"));
        }

        for (const auto &block : result.classes)
        {
            if (block.size() < 2)
                continue;
            std::ostringstream members;
            for (std::size_t i = 0; i < block.size(); ++i)
            {
                if (i != 0)
                    members << ", ";
                members << compact_log_text(
                    m_live_eq_terms.at(block[i]).to_string());
            }
            LOG_INFO(g_log, "eqpartition",
                     "complete equality class size=" +
                         std::to_string(block.size()) + " terms={" +
                         members.str() + "}");
        }

        expr_vector no_fixed(ctx());
        std::size_t partition_propagated = 0;
        for (const auto &[lhs_index, rhs_index] : result.proof_edges)
        {
            if (lhs_index >= m_live_eq_terms.size() ||
                rhs_index >= m_live_eq_terms.size())
                throw std::runtime_error(
                    "partition refiner returned an invalid term index");
            const std::uint64_t key =
                live_eq_pair_key(lhs_index, rhs_index);
            if (!m_live_eq_applied_keys.insert(key).second)
                continue;
            const expr &lhs = m_live_eq_terms[lhs_index];
            const expr &rhs = m_live_eq_terms[rhs_index];
            m_proved_global_eq.emplace_back(lhs, rhs);
            if (!g_cli.eq_gb_live_partition_refinement &&
                g_cli.eq_gb_live_propagate)
            {
                this->propagate(no_fixed, lhs == rhs);
                ++m_live_eq_propagated;
                ++partition_propagated;
            }
            ++m_live_eq_applied;
            ++m_live_eq_applied_at_final;
            LOG_INFO(g_log, "eqpartition",
                     "partition applied global equality: " +
                         compact_log_text(lhs.to_string()) + " == " +
                         compact_log_text(rhs.to_string()));
        }

        m_eq_partition_results_applied = true;
        m_live_eq_gb_pending_high_water = std::max(
            m_live_eq_gb_pending_high_water,
            m_proved_global_eq.size() - m_live_eq_gb_committed);

        const auto &stats = result.statistics;
        LOG_INFO(g_log, "eqpartition",
                 "partition summary: status=complete terms=" +
                     std::to_string(stats.terms) +
                     " blocks=" + std::to_string(stats.initial_blocks) +
                     "->" + std::to_string(stats.final_blocks) +
                     " checks=" + std::to_string(stats.checks) +
                     " sat=" + std::to_string(stats.sat_checks) +
                     " unsat=" + std::to_string(stats.unsat_checks) +
                     " refinements=" +
                     std::to_string(stats.refinements) +
                     " equality-classes=" +
                     std::to_string(stats.equality_classes) +
                     " proof-edges=" +
                     std::to_string(stats.proof_edges) +
                     " propagated=" +
                     std::to_string(partition_propagated) +
                     " implied-pairs=" +
                     std::to_string(stats.implied_pairs) +
                     " splitter-edges-total=" +
                     std::to_string(stats.splitter_edges) +
                     " splitter-edges-max=" +
                     std::to_string(stats.max_splitter_edges) +
                     " check-time=" +
                     util::fmt_duration(stats.check_time) +
                     " elapsed=" + util::fmt_duration(stats.elapsed));
        return flush_pending_live_eq_generators(true);
    }

    static std::uint64_t live_eq_pair_key(std::size_t lhs, std::size_t rhs)
    {
        if (rhs < lhs)
            std::swap(lhs, rhs);
        if (lhs > UINT32_MAX || rhs > UINT32_MAX)
            throw std::runtime_error("live equality term index exceeds 32 bits");
        return (static_cast<std::uint64_t>(lhs) << 32) |
               static_cast<std::uint64_t>(rhs);
    }

    std::size_t eq_union_root(std::size_t node) const
    {
        while (m_eq_union_parent[node] != node)
            node = m_eq_union_parent[node];
        return node;
    }

    bool eq_union(std::size_t lhs, std::size_t rhs)
    {
        lhs = eq_union_root(lhs);
        rhs = eq_union_root(rhs);
        if (lhs == rhs)
            return false;
        if (m_eq_union_size[lhs] < m_eq_union_size[rhs])
            std::swap(lhs, rhs);
        m_eq_union_trail.push_back({rhs, lhs, m_eq_union_size[lhs]});
        m_eq_union_parent[rhs] = lhs;
        m_eq_union_size[lhs] += m_eq_union_size[rhs];
        return true;
    }

    std::size_t add_equality_to_generator_forest(const expr &x, const expr &y)
    {
        auto xi = m_bv_to_eq_view_indices.find((Z3_ast)x);
        auto yi = m_bv_to_eq_view_indices.find((Z3_ast)y);
        if (xi == m_bv_to_eq_view_indices.end() || yi == m_bv_to_eq_view_indices.end())
            return 0;
        std::size_t added = 0;
        for (std::size_t lhs_idx : xi->second)
            for (std::size_t rhs_idx : yi->second)
                if (compatible_eq_views(lhs_idx, rhs_idx) && lhs_idx != rhs_idx &&
                    eq_union(lhs_idx, rhs_idx))
                    ++added;
        return added;
    }

    std::size_t activate_equality_fact(const expr &x, const expr &y,
                                       bool globally_proved = false,
                                       bool update_epoch = true)
    {
        auto [first, second] = canonical_eq_keys(x, y);
        const std::string key = eq_key(first, second);
        if (!m_active_eq_keys.insert(key).second)
            return 0;
        const std::size_t generator_count = add_equality_to_generator_forest(x, y);
        m_eq_facts.push_back(EqFact{x, y, first, second, generator_count,
                                    globally_proved});
        m_eq_generator_count += generator_count;
        if (generator_count != 0 && update_epoch)
            ++m_eq_generator_epoch;
        return generator_count;
    }

    void rollback_eq_union_forest(std::size_t size)
    {
        while (m_eq_union_trail.size() > size)
        {
            const EqUnionUndo undo = m_eq_union_trail.back();
            m_eq_union_trail.pop_back();
            m_eq_union_parent[undo.child] = undo.child;
            m_eq_union_size[undo.parent] = undo.old_parent_size;
        }
    }

    void rebuild_active_eq_index()
    {
        m_active_eq_keys.clear();
        m_eq_generator_count = 0;
        for (const EqFact &fact : m_eq_facts)
        {
            m_active_eq_keys.insert(eq_key(fact.first_key, fact.second_key));
            m_eq_generator_count += fact.generator_count;
        }
    }

    void initialize_eq_coeff_index()
    {
        m_bv_to_eq_view_indices.clear();
        for (std::size_t i = 0; i < m_eq_coeff_views.size(); ++i)
        {
            const expr &base = m_eq_coeff_views[i].original_base;
            if (is_bv_to_int_app(base))
                m_bv_to_eq_view_indices[(Z3_ast)base.arg(0)].push_back(i);
        }
        m_eq_union_parent.resize(m_eq_coeff_views.size());
        std::iota(m_eq_union_parent.begin(), m_eq_union_parent.end(), 0);
        m_eq_union_size.assign(m_eq_coeff_views.size(), 1);
        m_eq_union_trail.clear();
    }

    void register_eq_terms(const std::vector<expr> &all_bv_terms)
    {
        const bool gb_requires_ring_bv = eq_gb_generator_mode_enabled();
        if (m_eq_callback_options.registration == util::EqRegistrationMode::Existing &&
            !gb_requires_ring_bv)
            return;

        std::size_t before = m_registered_terms.size();
        if (m_eq_callback_options.registration != util::EqRegistrationMode::AllBv)
        {
            // Equality-derived GB generators are name-agnostic.  Register
            // every BV that has a coefficient variable in the current ring;
            // registering only terms mentioned by a hand-written eqP would
            // defeat the purpose when those assertions are omitted.
            for (const auto &entry : m_bv_to_eq_view_indices)
                tracked_add(expr(ctx(), entry.first));
        }
        else
        {
            for (const expr &term : all_bv_terms)
                tracked_add(term);
        }
        LOG_INFO(g_log, "eqcallback",
                 "eq registration mode=" +
                     std::string(gb_requires_ring_bv &&
                                         m_eq_callback_options.registration == util::EqRegistrationMode::Existing
                                     ? "ring-bv(eq-gb)"
                                     : util::eq_registration_mode_name(m_eq_callback_options.registration)) +
                     " added=" + std::to_string(m_registered_terms.size() - before) +
                     " total=" + std::to_string(m_registered_terms.size()));
    }

    void log_fixed(const expr &t, const expr &v)
    {
        if (t.is_numeral())
            return;
        if (t.is_bool() && (t.is_true() || t.is_false()))
            return;
        if (is_bv_to_int_app(t))
            return;
        if (!g_cli.print_fixed_all)
        {
            if (!t.is_app())
                return;
            const std::string decl_name = t.decl().name().str();
            if (decl_name.size() < 6 || decl_name.compare(0, 6, "eqmodP") != 0)
                return;
        }
        LOG_TRACE(g_log, "fixed", label_of(t) + " = " + v.to_string());
    }

    void log_propagate(const expr &from, const expr &infer)
    {
        if (!PRINT_PROPAGATE)
            return;

        LOG_TRACE(g_log, "propagate", label_of(from) + " ==> " + infer.to_string());
    }

    static std::string lbool_to_string(Z3_lbool v)
    {
        switch (v)
        {
        case Z3_L_FALSE:
            return "false";
        case Z3_L_TRUE:
            return "true";
        default:
            return "undef";
        }
    }

    void log_conflict_ants(const std::vector<expr> &ants_vec) const
    {
        std::ostringstream oss;
        oss << "antecedents(" << ants_vec.size() << ")";
        for (size_t i = 0; i < ants_vec.size(); ++i)
        {
            const expr &a = ants_vec[i];
            oss << "\n  [" << i << "] " << label_of(a);
            auto bit = m_bool_cache.find((Z3_ast)a);
            if (bit != m_bool_cache.end())
                oss << " = " << lbool_to_string(bit->second);
            else
                oss << " = <not-fixed-bool>";
        }
        LOG_INFO(g_log, "conflict", oss.str());
    }

    Z3_lbool lbool_of(const expr &a) const override
    {
        auto it = m_bool_cache.find((Z3_ast)a);
        if (it == m_bool_cache.end())
            return Z3_L_UNDEF;
        return it->second;
    }

    bool try_get_fixed_expr(const expr &t, expr &out) const
    {
        auto it = m_fixed_ast_cache.find((Z3_ast)t);
        if (it == m_fixed_ast_cache.end())
            return false;
        if (it->second == nullptr)
            return false;
        expr v(t.ctx(), it->second);
        out = v;
        return true;
    }

    void cache_fixed_expr(const expr &t, const expr &v)
    {
        Z3_ast key = (Z3_ast)t;
        Z3_ast val = (Z3_ast)v;
        if (key == nullptr || val == nullptr)
            return;

        auto it = m_fixed_ast_cache.find(key);
        if (it != m_fixed_ast_cache.end())
        {
            if (it->second == val)
                return;
            m_fixed_ast_trail.push_back({key, true, it->second});
            Z3_inc_ref((Z3_context)ctx(), it->second);
            Z3_dec_ref((Z3_context)ctx(), it->second);
            it->second = val;
            Z3_inc_ref((Z3_context)ctx(), val);
            return;
        }

        m_fixed_ast_trail.push_back({key, false, nullptr});
        m_fixed_ast_cache.emplace(key, val);
        Z3_inc_ref((Z3_context)ctx(), val);
    }

    void cache_bool_value(const expr &t, Z3_lbool bv)
    {
        Z3_ast key = (Z3_ast)t;
        auto it = m_bool_cache.find(key);
        if (it != m_bool_cache.end())
        {
            if (it->second == bv)
                return;
            m_bool_trail.push_back({key, true, it->second});
            it->second = bv;
            return;
        }

        m_bool_trail.push_back({key, false, Z3_L_UNDEF});
        m_bool_cache.emplace(key, bv);
    }

    void restore_fixed_ast_entry(const FixedAstTrailEntry &entry)
    {
        auto it = m_fixed_ast_cache.find(entry.key);
        if (it != m_fixed_ast_cache.end() && it->second != nullptr)
            Z3_dec_ref((Z3_context)ctx(), it->second);

        if (entry.had_old)
        {
            m_fixed_ast_cache[entry.key] = entry.old_value;
            if (entry.old_value != nullptr)
            {
                Z3_inc_ref((Z3_context)ctx(), entry.old_value);
                Z3_dec_ref((Z3_context)ctx(), entry.old_value);
            }
        }
        else if (it != m_fixed_ast_cache.end())
        {
            m_fixed_ast_cache.erase(it);
        }
    }

    static bool parse_z3_numeral_to_mpz(const expr &e, mpz_class &out)
    {
        if (!e.is_numeral())
            return false;
        Z3_string s = Z3_get_numeral_string((Z3_context)e.ctx(), (Z3_ast)e);
        mpz_class v;
        if (v.set_str(s, 10) != 0)
            return false;
        out = v;
        return true;
    }

    bool try_eval_bv_with_fixed_values(const expr &e, mpz_class &out) const
    {
        if (e.is_numeral() && e.get_sort().is_bv())
            return parse_z3_numeral_to_mpz(e, out);

        expr fv = e;
        if (try_get_fixed_expr(e, fv))
        {
            if (z3::eq(fv, e))
                return false;
            return try_eval_bv_with_fixed_values(fv, out);
        }

        return false;
    }

    bool try_eval_int_with_fixed_values(const expr &e, mpz_class &out) const
    {
        if (e.is_numeral() && e.get_sort().is_int())
            return parse_z3_numeral_to_mpz(e, out);

        expr fv = e;
        if (try_get_fixed_expr(e, fv))
        {
            if (z3::eq(fv, e))
                return false;
            return try_eval_int_with_fixed_values(fv, out);
        }

        if (!e.is_app())
            return false;

        const std::string op = e.decl().name().str();

        if (op == "-" && e.num_args() == 1)
        {
            mpz_class a;
            if (!try_eval_int_with_fixed_values(e.arg(0), a))
                return false;
            out = -a;
            return true;
        }

        if ((op == "+" || op == "-" || op == "*") && e.num_args() == 2)
        {
            mpz_class a, b;
            if (!try_eval_int_with_fixed_values(e.arg(0), a))
                return false;
            if (!try_eval_int_with_fixed_values(e.arg(1), b))
                return false;

            if (op == "+")
                out = a + b;
            else if (op == "-")
                out = a - b;
            else
                out = a * b;
            return true;
        }

        if (is_bv_to_int_app(e) && e.num_args() == 1)
        {
            mpz_class bv;
            if (!try_eval_bv_with_fixed_values(e.arg(0), bv))
                return false;
            out = bv;
            return true;
        }

        return false;
    }

    std::string true_context_source_signature() const override
    {
        // The old guard used only the number of TRUE atoms.  That both loses
        // the identity of the ideal and forces pop() to invalidate the guard
        // unconditionally.  Record the exact algebraic sources instead so a
        // previously computed membership result can be reused when search
        // backtracks to the same ideal.
        std::ostringstream signature;
        for (std::size_t i = 0; i < m_eqp.size(); ++i)
            if (m_eqp[i].D_full != nullptr &&
                lbool_of(m_eqp[i].atom) == Z3_L_TRUE)
                signature << "E" << i << ';';
        for (std::size_t i = 0; i < m_eqmodp.size(); ++i)
            if (m_eqmodp[i].true_gen != nullptr &&
                lbool_of(m_eqmodp[i].atom) == Z3_L_TRUE)
                signature << "P1" << i << ';';
        for (std::size_t i = 0; i < m_eqmodp2.size(); ++i)
            if (m_eqmodp2[i].true_gen != nullptr &&
                lbool_of(m_eqmodp2[i].atom) == Z3_L_TRUE)
                signature << "P2" << i << ';';
        for (std::size_t i = 0; i < m_eqmodp3.size(); ++i)
            if (m_eqmodp3[i].true_gen != nullptr &&
                lbool_of(m_eqmodp3[i].atom) == Z3_L_TRUE)
                signature << "P3" << i << ';';
        for (std::size_t i = 0; i < m_eqmodp4.size(); ++i)
            if (m_eqmodp4[i].true_gen != nullptr &&
                lbool_of(m_eqmodp4[i].atom) == Z3_L_TRUE)
                signature << "P4" << i << ';';

        if (eq_gb_generator_mode_enabled())
        {
            std::vector<std::string> equality_sources;
            equality_sources.reserve(m_eq_facts.size());
            for (const EqFact &fact : m_eq_facts)
            {
                const unsigned lhs_id = Z3_get_ast_id(
                    (Z3_context)fact.lhs.ctx(), (Z3_ast)fact.lhs);
                const unsigned rhs_id = Z3_get_ast_id(
                    (Z3_context)fact.rhs.ctx(), (Z3_ast)fact.rhs);
                equality_sources.push_back(
                    std::string(fact.globally_proved ? "G" : "L") +
                    std::to_string(std::min(lhs_id, rhs_id)) + ':' +
                    std::to_string(std::max(lhs_id, rhs_id)));
            }
            std::sort(equality_sources.begin(), equality_sources.end());
            for (const std::string &source : equality_sources)
                signature << source << ';';
        }
        return signature.str();
    }

    std::size_t true_context_atom_count() const override
    {
        std::size_t n = 0;
        for (const auto &ep : m_eqp)
            if (lbool_of(ep.atom) == Z3_L_TRUE)
                ++n;
        for (const auto &cp : m_eqmodp)
            if (lbool_of(cp.atom) == Z3_L_TRUE)
                ++n;
        for (const auto &cp : m_eqmodp2)
            if (lbool_of(cp.atom) == Z3_L_TRUE)
                ++n;
        for (const auto &cp : m_eqmodp3)
            if (lbool_of(cp.atom) == Z3_L_TRUE)
                ++n;
        for (const auto &cp : m_eqmodp4)
            if (lbool_of(cp.atom) == Z3_L_TRUE)
                ++n;
        return n;
    }

    std::size_t equality_generator_epoch() const override
    {
        return m_eq_generator_epoch;
    }

    bool all_eqp_fixed() const override
    {
        for (const auto &ep : m_eqp)
            if (lbool_of(ep.atom) == Z3_L_UNDEF)
                return false;
        return true;
    }

    static void collect_int_bv_subterms_rec(const expr &e,
                                            std::unordered_set<Z3_ast> &seen,
                                            std::vector<expr> &out)
    {
        if ((e.get_sort().is_int() || e.get_sort().is_bv()) && !e.is_numeral())
        {
            Z3_ast k = (Z3_ast)e;
            if (seen.insert(k).second)
                out.push_back(e);
        }
        for (unsigned i = 0; i < e.num_args(); ++i)
            collect_int_bv_subterms_rec(e.arg(i), seen, out);
    }

    static void collect_minimal_eval_terms_from_int_expr_rec(const expr &e,
                                                             std::unordered_set<Z3_ast> &seen,
                                                             std::vector<expr> &out)
    {
        if (e.get_sort().is_bv() && !e.is_numeral())
        {
            Z3_ast k = (Z3_ast)e;
            if (seen.insert(k).second)
                out.push_back(e);
            return;
        }

        if (e.is_const() && e.get_sort().is_int() && !e.is_numeral())
        {
            Z3_ast k = (Z3_ast)e;
            if (seen.insert(k).second)
                out.push_back(e);
            return;
        }

        if (is_bv_to_int_app(e))
        {
            collect_minimal_eval_terms_from_int_expr_rec(e.arg(0), seen, out);
            return;
        }

        if (!e.is_app())
            return;
        for (unsigned i = 0; i < e.num_args(); ++i)
            collect_minimal_eval_terms_from_int_expr_rec(e.arg(i), seen, out);
    }

    static void collect_minimal_eval_terms_from_polyterm_rec(const expr &p,
                                                             std::unordered_set<Z3_ast> &seen,
                                                             std::vector<expr> &out)
    {
        if (is_ctor(p, "PConst", 1))
        {
            collect_minimal_eval_terms_from_int_expr_rec(p.arg(0), seen, out);
            return;
        }
        if (is_ctor(p, "PNeg", 1))
        {
            collect_minimal_eval_terms_from_polyterm_rec(p.arg(0), seen, out);
            return;
        }
        if (is_ctor(p, "PAdd", 2) || is_ctor(p, "PSub", 2) || is_ctor(p, "PMul", 2))
        {
            collect_minimal_eval_terms_from_polyterm_rec(p.arg(0), seen, out);
            collect_minimal_eval_terms_from_polyterm_rec(p.arg(1), seen, out);
            return;
        }
        if (is_ctor(p, "PPow", 2))
        {
            collect_minimal_eval_terms_from_polyterm_rec(p.arg(0), seen, out);
            return;
        }
    }

    void register_watch_term(const expr &t)
    {
        Z3_ast k = (Z3_ast)t;
        if (!m_eval_watch_registered.insert(k).second)
            return;
        tracked_add(t);
    }

    void ensure_minimal_eval_watch_registered()
    {
        if (m_minimal_eval_watch_registered)
            return;

        std::size_t n = 0;
        for (const auto &base : m_cmap.z3_bases)
        {
            if (is_bv_to_int_app(base))
            {
                register_watch_term(base.arg(0));
                ++n;
            }
            else if (base.is_const() && base.get_sort().is_int() && !base.is_numeral())
            {
                register_watch_term(base);
                ++n;
            }
        }

        m_minimal_eval_watch_registered = true;
        LOG_INFO(g_log, "init",
                 "minimal fixed watch: registered " + std::to_string(n) +
                     " coeff base term(s) for final_fixed_value_check");
    }

    static void collect_eval_terms_from_polyterm_rec(const expr &p,
                                                     std::unordered_set<Z3_ast> &seen,
                                                     std::vector<expr> &out)
    {
        if (is_ctor(p, "PConst", 1))
        {
            collect_int_bv_subterms_rec(p.arg(0), seen, out);
            return;
        }
        if (is_ctor(p, "PNeg", 1))
        {
            collect_eval_terms_from_polyterm_rec(p.arg(0), seen, out);
            return;
        }
        if (is_ctor(p, "PAdd", 2) || is_ctor(p, "PSub", 2) || is_ctor(p, "PMul", 2))
        {
            collect_eval_terms_from_polyterm_rec(p.arg(0), seen, out);
            collect_eval_terms_from_polyterm_rec(p.arg(1), seen, out);
            return;
        }
        if (is_ctor(p, "PPow", 2))
        {
            collect_eval_terms_from_polyterm_rec(p.arg(0), seen, out);
            collect_int_bv_subterms_rec(p.arg(1), seen, out);
            return;
        }
    }

    void register_eval_terms_for_eqmod_atom(const expr &A, const expr &B, const expr &M)
    {
        (void)A;
        (void)B;
        (void)M;
        if (g_cli.enable_minimal_fixed_watch)
        {
            ensure_minimal_eval_watch_registered();
            return;
        }

        std::unordered_set<Z3_ast> seen;
        std::vector<expr> terms;
        collect_eval_terms_from_polyterm_rec(A, seen, terms);
        collect_eval_terms_from_polyterm_rec(B, seen, terms);
        collect_eval_terms_from_polyterm_rec(M, seen, terms);
        for (const auto &t : terms)
            tracked_add(t);
    }

    void register_eval_terms_for_eqmod_atom(const expr &A,
                                             const expr &B,
                                             const std::vector<expr> &moduli)
    {
        if (g_cli.enable_minimal_fixed_watch)
        {
            ensure_minimal_eval_watch_registered();
            return;
        }
        std::unordered_set<Z3_ast> seen;
        std::vector<expr> terms;
        collect_eval_terms_from_polyterm_rec(A, seen, terms);
        collect_eval_terms_from_polyterm_rec(B, seen, terms);
        for (const expr &modulus : moduli)
            collect_eval_terms_from_polyterm_rec(modulus, seen, terms);
        for (const expr &term : terms)
            tracked_add(term);
    }

    void collect_fixed_ants_from_polyterm(const expr &p,
                                          std::unordered_set<Z3_ast> &seen,
                                          std::vector<expr> &ants) const
    {
        std::unordered_set<Z3_ast> eval_seen;
        std::vector<expr> eval_terms;
        if (g_cli.enable_minimal_fixed_watch)
            collect_minimal_eval_terms_from_polyterm_rec(p, eval_seen, eval_terms);
        else
            collect_eval_terms_from_polyterm_rec(p, eval_seen, eval_terms);

        for (const auto &t : eval_terms)
        {
            expr v = t;
            if (!try_get_fixed_expr(t, v))
                continue;

            // Keep only terms that are concretely fixed now.
            if (!(v.is_numeral() || v.is_true() || v.is_false()))
                continue;

            Z3_ast k = (Z3_ast)t;
            if (seen.insert(k).second)
                ants.push_back(t);
        }
    }

    bool build_validation_assignments(
        const expr &A,
        const expr &B,
        const std::vector<expr> &modulus_terms,
        std::vector<poly> &assignments,
        std::string &skip_reason) override
    {
        std::unordered_set<Z3_ast> dependency_set;
        collect_coeff_bases_rec(A, dependency_set);
        collect_coeff_bases_rec(B, dependency_set);
        for (const expr &term : modulus_terms)
            collect_coeff_bases_rec(term, dependency_set);

        std::vector<unsigned> dependency_indices;
        dependency_indices.reserve(dependency_set.size());
        for (Z3_ast dependency : dependency_set)
        {
            auto found = m_cmap.base_to_index.find(dependency);
            if (found == m_cmap.base_to_index.end())
            {
                skip_reason = "coefficient-not-in-ring-map";
                return false;
            }
            dependency_indices.push_back(found->second);
        }
        std::sort(dependency_indices.begin(), dependency_indices.end());
        dependency_indices.erase(
            std::unique(dependency_indices.begin(), dependency_indices.end()),
            dependency_indices.end());

        ring R = m_RE.R;
        ScopedPolyVectorOwner assignments_owner(R);
        std::vector<poly> &owned = assignments_owner.values();
        owned.reserve(dependency_indices.size());
        for (unsigned index : dependency_indices)
        {
            const expr &base = m_cmap.z3_bases[index];
            mpz_class value;
            if (!try_eval_int_with_fixed_values(base, value))
            {
                skip_reason = "coefficient-without-fixed-value";
                return false;
            }
            ScopedPolyOwner variable(
                R, make_var_poly(m_RE, m_cmap.ring_names[index]));
            ScopedPolyOwner constant(R, poly_from_mpz(value, R));
            constant.reset(poly_negate_owned(constant.release(), R));
            owned.push_back(poly_add_owned(
                variable.release(), constant.release(), R));
        }
        assignments = assignments_owner.release();
        return true;
    }

    ProofPremises validation_conflict_premises(
        const expr &atom,
        const expr &A,
        const expr &B,
        const std::vector<expr> &modulus_terms) const override
    {
        ProofPremises premises;
        premises.fixed.push_back(atom);
        std::unordered_set<Z3_ast> seen{(Z3_ast)atom};
        collect_fixed_ants_from_polyterm(A, seen, premises.fixed);
        collect_fixed_ants_from_polyterm(B, seen, premises.fixed);
        for (const expr &term : modulus_terms)
            collect_fixed_ants_from_polyterm(term, seen, premises.fixed);
        return premises;
    }


    void add_and_propagate_all(const expr &ante, const std::vector<expr> &cons)
    {
        expr_vector ants(ctx());
        ants.push_back(ante);
        for (auto &cns : cons)
        {
            tracked_add(cns);
            log_propagate(ante, cns);
            this->propagate(ants, cns);
        }
    }

    void add_and_propagate_one(const expr &ante, const expr &conseq)
    {
        expr_vector ants(ctx());
        ants.push_back(ante);
        tracked_add(conseq);
        log_propagate(ante, conseq);
        this->propagate(ants, conseq);
    }

    void conflict_with(const std::vector<expr> &ants_vec)
    {
        if (g_cli.log_conflict_ants)
            log_conflict_ants(ants_vec);
        expr_vector ants(ctx());
        for (auto &a : ants_vec)
            ants.push_back(a);
        ++m_conflict_generation;
        this->conflict(ants);
    }

    void conflict_with(const ProofPremises &premises) override
    {
        if (g_cli.log_conflict_ants)
        {
            log_conflict_ants(premises.fixed);
            for (const auto &eq : premises.equalities)
                LOG_INFO(g_log, "propagator",
                         "conflict equality antecedent: " +
                             eq.first.to_string() + " == " +
                             eq.second.to_string());
        }
        expr_vector fixed(ctx()), lhs(ctx()), rhs(ctx());
        for (const expr &a : premises.fixed)
            fixed.push_back(a);
        for (const auto &eq : premises.equalities)
        {
            lhs.push_back(eq.first);
            rhs.push_back(eq.second);
        }
        ++m_conflict_generation;
        this->conflict(fixed, lhs, rhs);
    }

    static std::string compact_log_text(const std::string &text)
    {
        std::string out;
        out.reserve(text.size());
        bool pending_space = false;
        for (unsigned char ch : text)
        {
            if (std::isspace(ch))
            {
                pending_space = !out.empty();
                continue;
            }
            if (pending_space)
                out.push_back(' ');
            out.push_back(static_cast<char>(ch));
            pending_space = false;
        }
        return out;
    }

    void propagate_true_atom(
        const expr &atom, const ProofPremises &premises) override
    {
        expr_vector fixed(ctx()), lhs(ctx()), rhs(ctx());
        for (const expr &a : premises.fixed)
            fixed.push_back(a);
        for (const auto &eq : premises.equalities)
        {
            lhs.push_back(eq.first);
            rhs.push_back(eq.second);
        }
        tracked_add(atom);
        this->propagate(fixed, lhs, rhs, atom);
    }

    void trace_true_lemma_gb(
        bool begin,
        const std::string &label,
        std::size_t equality_generator_count,
        std::size_t total_generator_count) override
    {
        m_eq_callback_tracker.on_gb(
            eq_trace_enabled(), begin, label, m_eq_facts.size(),
            equality_generator_count, total_generator_count);
    }

    void collect_active_eq_source_generators(std::vector<SourceGenerator> &gens_out)
    {
        if (!eq_gb_generator_mode_enabled())
            return;
        ring R = m_RE.R;
        rChangeCurrRing(R);

        // Active equality sources can contain redundant paths through an
        // equality class.  Its difference ideal only needs a spanning forest:
        // for a=b, b=c, a=c, the third generator is redundant.  Build one
        // forest across all sources, while compatible_eq_views keeps unsigned
        // and signed BV-to-Int interpretations separate.
        std::vector<std::size_t> parent(m_eq_coeff_views.size());
        std::iota(parent.begin(), parent.end(), 0);
        auto find_root = [&parent](std::size_t node)
        {
            std::size_t root = node;
            while (parent[root] != root)
                root = parent[root];
            while (parent[node] != node)
            {
                const std::size_t next = parent[node];
                parent[node] = root;
                node = next;
            }
            return root;
        };

        for (const EqFact &fact : m_eq_facts)
        {
            auto lhs_it = m_bv_to_eq_view_indices.find((Z3_ast)fact.lhs);
            auto rhs_it = m_bv_to_eq_view_indices.find((Z3_ast)fact.rhs);
            if (lhs_it == m_bv_to_eq_view_indices.end() || rhs_it == m_bv_to_eq_view_indices.end())
                continue;
            for (std::size_t lhs_idx : lhs_it->second)
            {
                for (std::size_t rhs_idx : rhs_it->second)
                {
                    if (!compatible_eq_views(lhs_idx, rhs_idx) || lhs_idx == rhs_idx)
                        continue;
                    const std::size_t lhs_root = find_root(lhs_idx);
                    const std::size_t rhs_root = find_root(rhs_idx);
                    if (lhs_root == rhs_root)
                        continue;
                    parent[rhs_root] = lhs_root;
                    poly lhs_poly = expr_to_poly_anyring(
                        m_eq_coeff_views[lhs_idx].rewritten_int, m_RE, m_cmap);
                    poly rhs_poly = expr_to_poly_anyring(
                        m_eq_coeff_views[rhs_idx].rewritten_int, m_RE, m_cmap);
                    poly difference = poly_add_owned(lhs_poly, poly_negate_owned(rhs_poly, R), R);
                    add_source_generator(
                        gens_out, difference, std::nullopt,
                        fact.globally_proved
                            ? std::optional<std::pair<expr, expr>>{}
                            : std::make_optional(std::make_pair(fact.lhs, fact.rhs)));
                }
            }
        }

    }

    void collect_true_context_source_generators(
        std::vector<SourceGenerator> &gens_out) override
    {
        ring R = m_RE.R;
        rChangeCurrRing(R);

        for (const auto &ep : m_eqp)
        {
            if (ep.D_full == nullptr)
                continue;
            if (lbool_of(ep.atom) != Z3_L_TRUE)
                continue;
            add_source_generator(gens_out, p_Copy(ep.D_full, R), ep.atom);
        }

        for (const auto &cp : m_eqmodp)
        {
            if (cp.true_gen == nullptr)
                continue;
            if (lbool_of(cp.atom) != Z3_L_TRUE)
                continue;
            add_source_generator(gens_out, p_Copy(cp.true_gen, R), cp.atom);
        }

        for (const auto &cp : m_eqmodp2)
        {
            if (cp.true_gen == nullptr)
                continue;
            if (lbool_of(cp.atom) != Z3_L_TRUE)
                continue;
            add_source_generator(gens_out, p_Copy(cp.true_gen, R), cp.atom);
        }
        for (const auto &cp : m_eqmodp3)
        {
            if (cp.true_gen != nullptr && lbool_of(cp.atom) == Z3_L_TRUE)
                add_source_generator(gens_out, p_Copy(cp.true_gen, R), cp.atom);
        }
        for (const auto &cp : m_eqmodp4)
        {
            if (cp.true_gen != nullptr && lbool_of(cp.atom) == Z3_L_TRUE)
                add_source_generator(gens_out, p_Copy(cp.true_gen, R), cp.atom);
        }

        collect_active_eq_source_generators(gens_out);

        for (const auto &[a, b] : g_cli.inject_ideal_eq)
        {
            int idx_a = -1, idx_b = -1;
            for (size_t i = 0; i < m_cmap.z3_bases.size(); ++i)
            {
                std::string bname = coeff_base_pretty_name(m_cmap.z3_bases[i]);
                if (bname == a)
                    idx_a = (int)i;
                if (bname == b)
                    idx_b = (int)i;
            }
            if (idx_a < 0 || idx_b < 0)
            {
                LOG_INFO(g_log, "inject",
                         "[inject-ideal-eq] skipped " + a + " - " + b +
                             " (not found in cmap: a=" + std::to_string(idx_a) +
                             " b=" + std::to_string(idx_b) + ")");
                continue;
            }
            const std::string &rn_a = m_cmap.ring_names[idx_a];
            const std::string &rn_b = m_cmap.ring_names[idx_b];
            poly pa = make_var_poly(m_RE, rn_a);
            poly pb = make_var_poly(m_RE, rn_b);
            poly diff = poly_add_owned(pa, poly_negate_owned(pb, R), R);
            add_source_generator(gens_out, diff, std::nullopt);
            LOG_INFO(g_log, "inject",
                     "[inject-ideal-eq] added " + rn_a + " - " + rn_b +
                         " to ideal (from " + a + " - " + b + ")");
        }
    }

    void on_fixed_eqP(const expr &atom, Z3_lbool bv)
    {
        for (auto &cp : m_eqp)
        {
            if (!z3::eq(atom, cp.atom))
                continue;

            if (bv == Z3_L_TRUE)
            {
                if (!cp.always_equal)
                {
                    for (auto &eq0 : cp.coeff_eqs)
                    {
                        if (eq0.is_false())
                        {
                            conflict_with({atom});
                            return;
                        }
                    }
                    add_and_propagate_all(atom, cp.coeff_eqs);
                }
                return;
            }

            if (bv == Z3_L_FALSE)
            {
                // For an opaque polynomial relation, D != 0 cannot be
                // expressed as a disjunction of Z3 coefficient constraints.
                // Keep this direction conservative (no propagation).
                if (cp.relational && !cp.always_equal)
                    return;
                if (cp.coeff_neq_disj.is_false())
                {
                    conflict_with({atom});
                    return;
                }
                add_and_propagate_one(atom, cp.coeff_neq_disj);
                return;
            }
        }
    }

    void check_eqmodP1_conflicts()
    {
        if (conflict_on_propagated_p1_truth())
            return;
        check_cross_family_eqmod_refutations();
    }

    bool all_eqp_eqmodp_fixed() const
    {
        for (const auto &ep : m_eqp)
        {
            if (lbool_of(ep.atom) == Z3_L_UNDEF)
                return false;
        }
        for (const auto &cp : m_eqmodp)
        {
            if (lbool_of(cp.atom) == Z3_L_UNDEF)
                return false;
        }
        return true;
    }

    void check_eqmodP1_conflicts_when_ready()
    {
        if (m_eqmodp.empty())
            return;
        if (conflict_on_propagated_p1_truth())
            return;
        if (!all_eqp_eqmodp_fixed())
            return;
        check_eqmodP1_conflicts();
    }

    bool all_eqp_eqmodp2_fixed() const
    {
        for (const auto &ep : m_eqp)
        {
            if (lbool_of(ep.atom) == Z3_L_UNDEF)
                return false;
        }
        for (const auto &cp : m_eqmodp2)
        {
            if (lbool_of(cp.atom) == Z3_L_UNDEF)
                return false;
        }
        return true;
    }

    void check_eqmodP2_conflicts()
    {
        if (conflict_on_propagated_p2_truth())
            return;
        check_cross_family_eqmod_refutations();
    }

    void check_eqmodP2_conflicts_when_ready()
    {
        if (m_eqmodp2.empty())
            return;
        if (conflict_on_propagated_p2_truth())
            return;
        if (!all_eqp_eqmodp2_fixed())
            return;
        check_eqmodP2_conflicts();
    }

    void check_eqmodN_conflicts_when_ready()
    {
        if (conflict_on_propagated_n_truth())
            return;
        check_cross_family_eqmod_refutations();
    }

public:
    PolyPropagator(solver *s,
                   const std::vector<expr> &eqps,
                   const std::vector<expr> &lhs,
                   const std::vector<expr> &rhs,
                   const std::vector<expr> &eqmodsP1,
                   const std::vector<std::vector<expr>> &eqmodn_atoms,
                   const IndetEnv &env,
                   const CoeffVarMap &cmap,
                   const std::vector<std::string> &indet_ring_names,
                   const std::vector<std::string> &ring_vars,
                   const std::vector<std::string> &qvar_names,
                   const std::vector<std::vector<std::vector<std::string>>> &eqmodn_qvar_names,
                   const util::EqCallbackOptions &eq_callback_options,
                   const std::vector<expr> &all_bv_terms,
                   const std::vector<RewrittenCoeffBase> &eq_coeff_views,
                   const std::vector<expr> &online_bv_constraints,
                   const std::vector<expr> &online_bv_terms,
                   const std::vector<std::pair<expr, expr>> &partition_prepass_equalities,
                   const std::vector<expr> &partition_prepass_triggers)
        : user_propagator_base(s),
          eqmod::EqmodEngine(qvar_names, eqmodn_qvar_names,
                             eqmodsP1, eqmodn_atoms),
          m_env(env), m_cmap(cmap),
          m_indet_ring_names(indet_ring_names), m_ring_vars(ring_vars),
          m_eq_callback_options(eq_callback_options),
          m_eq_callback_tracker(g_log, true),
          m_all_bv_terms(all_bv_terms),
          m_eq_coeff_views(eq_coeff_views),
          m_online_bv_constraints(online_bv_constraints),
          m_online_bv_terms(online_bv_terms),
          m_partition_prepass_equalities(partition_prepass_equalities),
          m_partition_prepass_triggers(partition_prepass_triggers)
    {
        init_singular();

        register_fixed();
        register_eq();
        register_final();
        register_created();

        for (const expr &trigger : m_partition_prepass_triggers)
            tracked_add(trigger);

        m_Nc = (int)m_cmap.z3_bases.size();
        m_Mi = (int)m_env.split_indet_count;
        m_eqmod_collected_atoms[1] = eqmodsP1.size();
        for (unsigned arity = 2; arity <= 4; ++arity)
            if (eqmodn_atoms.size() > arity)
                m_eqmod_collected_atoms[arity] = eqmodn_atoms[arity].size();

        coeffs cfZ = nCopyCoeff(singular_shared_coeffs_Z());

        m_RE.build(cfZ, m_ring_vars, ringorder_lp);
        bind_ring(m_RE.R);
        dump_ring(m_RE.R);
        bind_ring_indices(
            m_cmap, m_RE, m_indet_ring_names, m_env.split_indet_count);
        initialize_eq_coeff_index();
        initialize_gb_process_pool();
        initialize_live_eq_validator();
        register_eq_terms(all_bv_terms);

        if (g_cli.enable_minimal_fixed_watch)
            ensure_minimal_eval_watch_registered();

        for (size_t i = 0; i < eqps.size(); ++i)
        {
            tracked_add(eqps[i]);
            if (!g_cli.enable_minimal_fixed_watch)
            {
                tracked_add(lhs[i]);
                tracked_add(rhs[i]);
            }

            std::string label = "eqP#" + std::to_string(i);
            m_label[(Z3_ast)eqps[i]] = label;

            EqPCompiled cp = compile_eqP_singular(eqps[i], lhs[i], rhs[i],
                                                  label,
                                                  m_env, m_indet_ring_names, m_RE, m_cmap,
                                                  m_Nc, m_Mi);

            for (auto &e : cp.coeff_eqs)
                tracked_add(e);
            tracked_add(cp.coeff_neq_disj);
            if (!g_cli.enable_minimal_fixed_watch)
            {
                for (auto &ci : cp.coeff_ints)
                    tracked_add(ci);
            }

            m_eqp.push_back(std::move(cp));
        }

        util::eqmod::require_preallocated_qvar_slots(
            eqmodsP1.size(), m_qvar_names, m_eqmodn_atoms,
            m_eqmodn_qvar_names);

        for (size_t i = 0; i < eqmodsP1.size(); ++i)
        {
            auto &em = eqmodsP1[i];
            register_slot(em, 1, i);
            tracked_add(em);
            if (!g_cli.enable_minimal_fixed_watch)
            {
                for (unsigned j = 0; j < 3; ++j)
                    tracked_add(em.arg(j));
            }
            register_eval_terms_for_eqmod_atom(em.arg(0), em.arg(1), em.arg(2));

            std::string label = "eqmodP1#" + std::to_string(i);
            m_label[(Z3_ast)em] = label;

            lower_atom(em, 1, label, m_env, m_indet_ring_names, m_RE,
                       m_cmap, m_Nc, g_log);
        }

        for (unsigned arity = 2; arity <= 4; ++arity)
        {
            for (size_t i = 0; i < m_eqmodn_atoms[arity].size(); ++i)
            {
                expr em = m_eqmodn_atoms[arity][i];
                register_slot(em, arity, i);
                tracked_add(em);
                if (!g_cli.enable_minimal_fixed_watch)
                    for (unsigned j = 0; j < em.num_args(); ++j)
                        tracked_add(em.arg(j));
                std::vector<expr> moduli;
                for (unsigned j = 2; j < em.num_args(); ++j)
                    moduli.push_back(em.arg(j));
                register_eval_terms_for_eqmod_atom(em.arg(0), em.arg(1), moduli);

                std::string label = "eqmodP" + std::to_string(arity) + "#" + std::to_string(i);
                m_label[(Z3_ast)em] = label;
                lower_atom(em, arity, label, m_env, m_indet_ring_names, m_RE,
                           m_cmap, m_Nc, g_log);
            }
        }

    }

    PolyPropagator(context &c,
                   const IndetEnv &env,
                   const CoeffVarMap &cmap,
                   const std::vector<std::string> &indet_ring_names,
                   const std::vector<std::string> &ring_vars,
                   const std::vector<std::string> &qvar_names,
                   const std::vector<std::vector<std::vector<std::string>>> &eqmodn_qvar_names,
                   const std::vector<expr> &eqmodp1_atoms,
                   const std::vector<std::vector<expr>> &eqmodn_atoms,
                   const util::EqCallbackOptions &eq_callback_options,
                   const std::vector<expr> &all_bv_terms,
                   const std::vector<RewrittenCoeffBase> &eq_coeff_views,
                   const std::vector<expr> &online_bv_constraints,
                   const std::vector<expr> &online_bv_terms,
                   const std::vector<std::pair<expr, expr>> &partition_prepass_equalities,
                   const std::vector<expr> &partition_prepass_triggers)
        : user_propagator_base(c),
          eqmod::EqmodEngine(qvar_names, eqmodn_qvar_names),
          m_env(env), m_cmap(cmap),
          m_indet_ring_names(indet_ring_names), m_ring_vars(ring_vars),
          m_eq_callback_options(eq_callback_options),
          m_eq_callback_tracker(g_log, false),
          m_allow_live_validator(false)
    {
        util::eqmod::translate_atom_slots(
            c, eqmodp1_atoms, eqmodn_atoms, m_eqmodp1_atoms,
            m_eqmodp1_slots, m_eqmodn_atoms, m_eqmodn_slots);
        util::eqmod::require_preallocated_qvar_slots(
            m_eqmodp1_atoms.size(), m_qvar_names, m_eqmodn_atoms,
            m_eqmodn_qvar_names);
        m_eqmod_collected_atoms[1] = m_eqmodp1_atoms.size();
        for (unsigned arity = 2; arity <= 4; ++arity)
            m_eqmod_collected_atoms[arity] = m_eqmodn_atoms[arity].size();
        m_cmap.base_to_index.clear();
        for (std::size_t i = 0; i < m_cmap.z3_bases.size(); ++i)
        {
            const expr &old_base = m_cmap.z3_bases[i];
            m_cmap.z3_bases[i] = expr(c, Z3_translate((Z3_context)old_base.ctx(),
                                                      (Z3_ast)old_base, (Z3_context)c));
            m_cmap.base_to_index[(Z3_ast)m_cmap.z3_bases[i]] = static_cast<unsigned>(i);
        }
        m_all_bv_terms.reserve(all_bv_terms.size());
        for (const expr &term : all_bv_terms)
            m_all_bv_terms.emplace_back(c, Z3_translate((Z3_context)term.ctx(),
                                                        (Z3_ast)term, (Z3_context)c));
        m_eq_coeff_views.reserve(eq_coeff_views.size());
        for (const RewrittenCoeffBase &view : eq_coeff_views)
        {
            expr original(c, Z3_translate((Z3_context)view.original_base.ctx(),
                                          (Z3_ast)view.original_base, (Z3_context)c));
            expr rewritten(c, Z3_translate((Z3_context)view.rewritten_int.ctx(),
                                           (Z3_ast)view.rewritten_int, (Z3_context)c));
            m_eq_coeff_views.emplace_back(original, rewritten);
        }
        m_online_bv_constraints.reserve(online_bv_constraints.size());
        for (const expr &constraint : online_bv_constraints)
            m_online_bv_constraints.emplace_back(
                c, Z3_translate((Z3_context)constraint.ctx(), (Z3_ast)constraint,
                                (Z3_context)c));
        m_online_bv_terms.reserve(online_bv_terms.size());
        for (const expr &term : online_bv_terms)
            m_online_bv_terms.emplace_back(
                c, Z3_translate((Z3_context)term.ctx(), (Z3_ast)term,
                                (Z3_context)c));
        m_partition_prepass_equalities.reserve(
            partition_prepass_equalities.size());
        for (const auto &[lhs, rhs] : partition_prepass_equalities)
            m_partition_prepass_equalities.emplace_back(
                expr(c, Z3_translate((Z3_context)lhs.ctx(), (Z3_ast)lhs,
                                     (Z3_context)c)),
                expr(c, Z3_translate((Z3_context)rhs.ctx(), (Z3_ast)rhs,
                                     (Z3_context)c)));
        m_partition_prepass_triggers.reserve(partition_prepass_triggers.size());
        for (const expr &trigger : partition_prepass_triggers)
            m_partition_prepass_triggers.emplace_back(
                c, Z3_translate((Z3_context)trigger.ctx(), (Z3_ast)trigger,
                                (Z3_context)c));

        init_singular();
        register_fixed();
        register_eq();
        register_final();
        register_created();

        m_Nc = (int)m_cmap.z3_bases.size();
        m_Mi = (int)m_env.split_indet_count;

        coeffs cfZ = nCopyCoeff(singular_shared_coeffs_Z());

        m_RE.build(cfZ, m_ring_vars, ringorder_lp);
        bind_ring(m_RE.R);
        dump_ring(m_RE.R);
        bind_ring_indices(
            m_cmap, m_RE, m_indet_ring_names, m_env.split_indet_count);
        initialize_eq_coeff_index();
        initialize_gb_process_pool();
        initialize_live_eq_validator();
        register_eq_terms(m_all_bv_terms);
    }

    ~PolyPropagator() override
    {
        for (auto &entry : m_fixed_ast_trail)
            if (entry.had_old && entry.old_value != nullptr)
                Z3_dec_ref((Z3_context)ctx(), entry.old_value);
        m_fixed_ast_trail.clear();
        m_bool_trail.clear();
        m_trail_marks.clear();

        for (auto &kv : m_fixed_ast_cache)
            if (kv.second != nullptr)
                Z3_dec_ref((Z3_context)ctx(), kv.second);
        m_fixed_ast_cache.clear();

        ring R = m_RE.R;
        if (R)
        {
            rChangeCurrRing(R);

            release();

            for (auto &ep : m_eqp)
            {
                if (ep.D_full)
                    p_Delete(&ep.D_full, R);
                ep.D_full = nullptr;
            }

        }
    }

    void push() override
    {
        m_trail_marks.push_back({m_bool_trail.size(), m_fixed_ast_trail.size(),
                                 m_eq_facts.size(), m_eq_union_trail.size(),
                                 m_live_eq_union_trail.size()});
        m_eq_callback_tracker.on_push(eq_trace_enabled(), m_eq_facts.size());
        ++m_search_push_count;
        if (m_trail_marks.size() > m_search_max_depth)
            m_search_max_depth = m_trail_marks.size();
        search_progress_tick("push");
    }

    void pop(unsigned n) override
    {
        const unsigned requested_n = n;
        const std::size_t old_scope_depth = m_trail_marks.size();
        const std::size_t old_active_eq = m_eq_facts.size();
        const std::size_t old_eq_generators = m_eq_generator_count;
        while (n-- > 0 && !m_trail_marks.empty())
        {
            TrailMark mark = m_trail_marks.back();
            m_trail_marks.pop_back();

            while (m_bool_trail.size() > mark.bool_size)
            {
                BoolTrailEntry entry = m_bool_trail.back();
                m_bool_trail.pop_back();
                if (entry.had_old)
                    m_bool_cache[entry.key] = entry.old_value;
                else
                    m_bool_cache.erase(entry.key);
            }

            while (m_fixed_ast_trail.size() > mark.fixed_ast_size)
            {
                FixedAstTrailEntry entry = m_fixed_ast_trail.back();
                m_fixed_ast_trail.pop_back();
                restore_fixed_ast_entry(entry);
            }

            // Live GB facts enter this forest only after their equality has
            // been proved global.  They are premise-free facts of the whole
            // problem, not facts of the current Z3 search scope, so a pop
            // must not remove them or roll back their union-forest edges.
            // Non-live equality tracking remains scoped as before.
            if (!g_cli.enable_eq_gb_live && m_eq_facts.size() > mark.eq_size)
            {
                const std::size_t old_generator_count = m_eq_generator_count;
                m_eq_facts.erase(
                    m_eq_facts.begin() + static_cast<std::ptrdiff_t>(mark.eq_size),
                    m_eq_facts.end());
                rollback_eq_union_forest(mark.eq_union_size);
                rebuild_active_eq_index();
                if (m_eq_generator_count != old_generator_count)
                    ++m_eq_generator_epoch;
            }

            rollback_live_eq_union(mark.live_eq_union_size);

            reset_after_pop(g_cli.enable_eq_gb_live);
        }
        m_eq_callback_tracker.on_pop(eq_trace_enabled(), requested_n, m_eq_facts.size());
        ++m_search_pop_count;
        search_progress_tick("pop");
        if (m_eq_generator_count != old_eq_generators)
            LOG_INFO(g_log, "eqgb",
                     "pop count=" + std::to_string(requested_n) +
                         " scope=" + std::to_string(old_scope_depth) +
                         "->" + std::to_string(m_trail_marks.size()) +
                         " active_eq=" + std::to_string(old_active_eq) +
                         "->" + std::to_string(m_eq_facts.size()) +
                         " eq_gens=" + std::to_string(old_eq_generators) +
                         "->" + std::to_string(m_eq_generator_count) +
                         " epoch=" + std::to_string(m_eq_generator_epoch));
    }
    void eq(const expr &x, const expr &y) override
    {
        ++m_search_eq_count;
        search_progress_tick("eq");
        if (eq_gb_live_heuristic_enabled())
            drain_live_eq_results(false);
        if (eq_gb_live_heuristic_enabled())
            submit_live_eq_candidate(x, y);
        const bool track_fact = eq_fact_tracking_enabled();
        bool globally_valid = !eq_gb_generator_mode_enabled();
        if (g_cli.enable_eq_gb_live)
            globally_valid = live_eq_is_applied(x, y);
        // Live global equalities are committed to the GB forest only by
        // flush_pending_live_eq_generators().  Re-activating one from the
        // Main Solver callback would bypass batching and recreate the
        // membership-recomputation storm this path is designed to avoid.
        if (track_fact && globally_valid && !g_cli.enable_eq_gb_live)
            activate_equality_fact(x, y, eq_gb_generator_mode_enabled());

        m_eq_callback_tracker.on_eq(x, y,
                              [this](const expr &e)
                              {
                                  return is_registered_term(e);
                              },
                              [this](const expr &e)
                              {
                                  return format_fixed_value_for_log(e);
                              },
                              eq_trace_enabled(), m_eq_facts.size(), m_eq_generator_count);

    }

    void created(const expr &t) override
    {
        ++m_search_created_count;
        search_progress_tick("created");
        if (!t.is_app())
            return;

        if (t.decl().name().str() == "eqP" && t.num_args() == 2)
        {
            expr A = t.arg(0), B = t.arg(1);
            tracked_add(t);
            if (!g_cli.enable_minimal_fixed_watch)
            {
                tracked_add(A);
                tracked_add(B);
            }

            std::string label = "eqP#" + std::to_string((int)m_eqp.size());
            m_label[(Z3_ast)t] = label;

            EqPCompiled cp = compile_eqP_singular(t, A, B,
                                                  label,
                                                  m_env, m_indet_ring_names, m_RE, m_cmap,
                                                  m_Nc, m_Mi);

            for (auto &e : cp.coeff_eqs)
                tracked_add(e);
            tracked_add(cp.coeff_neq_disj);
            if (!g_cli.enable_minimal_fixed_watch)
            {
                for (auto &ci : cp.coeff_ints)
                    tracked_add(ci);
            }

            m_eqp.push_back(std::move(cp));

            check_eqmodP1_conflicts_when_ready();
            check_eqmodP2_conflicts_when_ready();
            return;
        }

        if (t.decl().name().str() == "eqmodP1" && t.num_args() == 3)
        {
            if (is_compiled(t))
                return;
            expr A = t.arg(0), B = t.arg(1), M = t.arg(2);
            tracked_add(t);
            if (!g_cli.enable_minimal_fixed_watch)
            {
                tracked_add(A);
                tracked_add(B);
                tracked_add(M);
            }
            register_eval_terms_for_eqmod_atom(A, B, M);

            size_t idx = require_slot(t, 1, "created");

            std::string label = "eqmodP1#" + std::to_string((int)idx);
            m_label[(Z3_ast)t] = label;

            lower_atom(t, 1, label, m_env, m_indet_ring_names, m_RE,
                       m_cmap, m_Nc, g_log);

            propagate_eqmod_true_lemmas_from_context();
            check_eqmodP1_conflicts_when_ready();
            check_eqmodP2_conflicts_when_ready();
            return;
        }

        const std::string eqmod_name = t.decl().name().str();
        if ((eqmod_name == "eqmodP2" || eqmod_name == "eqmodP3" ||
             eqmod_name == "eqmodP4") &&
            t.num_args() >= 4 && t.num_args() <= 6)
        {
            if (is_compiled(t))
                return;

            const unsigned arity = t.num_args() - 2;
            if (eqmod_name != "eqmodP" + std::to_string(arity))
                return;
            expr A = t.arg(0), B = t.arg(1);
            tracked_add(t);
            if (!g_cli.enable_minimal_fixed_watch)
                for (unsigned i = 0; i < t.num_args(); ++i)
                    tracked_add(t.arg(i));
            std::vector<expr> moduli;
            for (unsigned i = 2; i < t.num_args(); ++i)
                moduli.push_back(t.arg(i));
            register_eval_terms_for_eqmod_atom(A, B, moduli);

            size_t idx = require_slot(t, arity, "created");

            std::string label = eqmod_name + "#" + std::to_string(idx);
            m_label[(Z3_ast)t] = label;

            lower_atom(t, arity, label, m_env, m_indet_ring_names, m_RE,
                       m_cmap, m_Nc, g_log);

            propagate_eqmod_true_lemmas_from_context();
            check_eqmodN_conflicts_when_ready();
            return;
        }
    }

    void fixed(const expr &t, const expr &v) override
    {
        ++m_search_fixed_count;
        propagate_partition_prepass_equalities(t, v);
        if (eq_gb_live_heuristic_enabled())
            (void)drain_live_eq_results(false);
        if (g_cli.enable_minimal_fixed_watch && !t.is_bool())
        {
            cache_fixed_expr(t, v);
            m_eq_callback_tracker.on_fixed(t, v, eq_trace_enabled());
            search_progress_tick("fixed");
            return;
        }

        ++m_search_fixed_bool_count;
        search_progress_tick("fixed");
        cli::report::ScopedAccumulatedTiming timing(
            g_final_fixed_value_check_timing,
            &g_final_fixed_value_check_span_start);
        log_fixed(t, v);
        cache_fixed_expr(t, v);
        m_eq_callback_tracker.on_fixed(t, v, eq_trace_enabled());

        if (t.is_numeral())
            return;

        if (t.is_bool())
        {
            Z3_lbool bv = Z3_get_bool_value(ctx(), (Z3_ast)v);
            cache_bool_value(t, bv);

            if (t.is_app() && t.decl().name().str() == "eqP" && t.num_args() == 2)
            {
                on_fixed_eqP(t, bv);
                propagate_eqmod_true_lemmas_from_context();
                check_eqmodP1_conflicts_when_ready();
                check_eqmodP2_conflicts_when_ready();
                check_eqmodN_conflicts_when_ready();
            }

            if (t.is_app() && t.decl().name().str() == "eqmodP1" && t.num_args() == 3)
            {
                propagate_eqmod_true_lemmas_from_context();
                check_eqmodP1_conflicts_when_ready();
                check_eqmodP2_conflicts_when_ready();
                check_eqmodN_conflicts_when_ready();
            }

            if (t.is_app() && t.decl().name().str() == "eqmodP2" && t.num_args() == 4)
            {
                propagate_eqmod_true_lemmas_from_context();
                check_eqmodP2_conflicts_when_ready();
                check_eqmodN_conflicts_when_ready();
            }

            if (t.is_app() &&
                (t.decl().name().str() == "eqmodP3" ||
                 t.decl().name().str() == "eqmodP4") &&
                t.num_args() >= 5 && t.num_args() <= 6)
            {
                propagate_eqmod_true_lemmas_from_context();
                check_eqmodN_conflicts_when_ready();
            }
        }
    }

    void final() override
    {
        ++m_search_final_count;
        {
            auto now = search_clk::now();
            LOG_INFO(g_log, "search",
                     "[final #" + std::to_string(m_search_final_count) +
                     " " + util::fmt_duration(now - m_search_start) + "] "
                     "depth=" + std::to_string(m_trail_marks.size()) +
                     " max_depth=" + std::to_string(m_search_max_depth) +
                     " push=" + std::to_string(m_search_push_count) +
                     " pop=" + std::to_string(m_search_pop_count) +
                     " fixed=" + std::to_string(m_search_fixed_count) +
                     " fixed_bool=" + std::to_string(m_search_fixed_bool_count) +
                     " eq=" + std::to_string(m_search_eq_count) +
                     " created=" + std::to_string(m_search_created_count));
        }
        bool handled_live_true_lemmas = false;
        if (g_cli.enable_eq_gb_live)
        {
            m_live_eq_in_final = true;
            handled_live_true_lemmas = true;
            if (eq_gb_live_heuristic_enabled())
            {
                m_live_eq_validator->release();
                while (true)
                {
                    ++m_live_eq_final_waves;
                    const std::size_t conflict_before = m_conflict_generation;

                    std::size_t wave_generators = drain_live_eq_results(false);
                    const std::size_t gb_pending =
                        m_proved_global_eq.size() - m_live_eq_gb_committed;
                    const bool validator_idle = m_live_eq_validator->idle();
                    if (validator_idle || gb_pending >= LIVE_EQ_GB_BATCH_SIZE)
                        wave_generators += flush_pending_live_eq_generators(true);
                    else
                        wave_generators += flush_pending_live_eq_generators(false);
                    if (wave_generators != 0)
                        LOG_INFO(g_log, "eqgb",
                                 "activated " + std::to_string(wave_generators) +
                                     " globally proved GB generator(s) in final wave");

                    propagate_eqmod_true_lemmas_from_context(true);
                    if (wave_generators != 0)
                        check_cross_family_eqmod_refutations(true);

                    // A propagation does not guarantee that Z3 will invoke
                    // final() again when the consequence is already consistent.
                    // Keep the completeness barrier until all callback candidates
                    // are terminal; a conflict is the only safe early return.
                    if (m_conflict_generation != conflict_before || validator_idle)
                        break;

                    const auto wait_started = search_clk::now();
                    ++m_live_eq_final_waits;
                    m_live_eq_validator->wait_for_results_or_idle();
                    m_live_eq_final_wait_time +=
                        std::chrono::duration_cast<std::chrono::nanoseconds>(
                            search_clk::now() - wait_started);
                }
            }

            if (eq_gb_partition_refinement_enabled())
            {
                const std::size_t complete_generators =
                    apply_partition_refinement_results();
                if (complete_generators != 0)
                    LOG_INFO(g_log, "eqpartition",
                             "activated " +
                                 std::to_string(complete_generators) +
                                 " complete-partition GB generator(s)");
                propagate_eqmod_true_lemmas_from_context(true);
                if (complete_generators != 0)
                    check_cross_family_eqmod_refutations(true);
            }
            m_live_eq_in_final = false;
        }
        if (!handled_live_true_lemmas)
            propagate_eqmod_true_lemmas_from_context(true);
        check_cross_family_eqmod_refutations(true);
        if (g_cli.enable_final_fixed_value_check)
        {
            cli::report::ScopedAccumulatedTiming timing(
                g_final_fixed_value_check_timing,
                &g_final_fixed_value_check_span_start);
            final_fixed_value_check_all_eqmods();
        }
        if (eq_trace_enabled())
        {
            m_eq_callback_tracker.print_summary(std::cout);
            LOG_INFO(g_log, "eqstats",
                     "registered=" + std::to_string(m_registered_terms.size()) +
                         " fixed=" + std::to_string(m_eq_callback_tracker.fixed_event_count()) +
                         " eq=" + std::to_string(m_eq_callback_tracker.eq_event_count()) +
                         " active_eq=" + std::to_string(m_eq_facts.size()) +
                         " eq_generators=" + std::to_string(m_eq_generator_count));
        }
        if (g_cli.enable_eqmod_true_lemmas && g_cli.enable_eq_gb_live)
            LOG_INFO(g_log, "singular",
                     "eqmod TRUE-lemma membership cache: signatures=" +
                         std::to_string(m_eqmod_true_lemma_membership_cache.size()) +
                         " hits=" +
                         std::to_string(m_eqmod_true_lemma_cache_hits) +
                         " misses=" +
                         std::to_string(m_eqmod_true_lemma_cache_misses) +
                         " deferred=" +
                         std::to_string(m_deferred_eqmod_true_lemma_checks) +
                         " pending-source-updates=" +
                         std::to_string(m_pending_eqmod_true_lemma_source_updates));
        if (g_cli.enable_eq_gb_live && m_live_eq_validator)
        {
            const util::eqgb::LiveValidatorStatistics stats =
                m_live_eq_validator->statistics();
            const std::size_t gb_pending =
                g_cli.eq_gb_live_generators
                    ? m_proved_global_eq.size() - m_live_eq_gb_committed
                    : 0;
            LOG_INFO(g_log, "eqgb",
                     "live validator summary: propagation=" +
                         std::string(g_cli.eq_gb_live_propagate ? "on" : "off") +
                         " generators=" +
                         std::string(g_cli.eq_gb_live_generators ? "on" : "off") +
                         " seed-models=" +
                         std::string(g_cli.eq_gb_live_seed_models ? "on" : "off") +
                         " queue-policy=" +
                         std::string(g_cli.eq_gb_live_unified_queue
                                         ? "unified"
                                         : "split-direct-derived") +
                         " survivor-policy=origin-64" +
                         " callback_seen=" +
                         std::to_string(stats.callback_candidates) +
                         " validator-direct=" +
                         std::to_string(stats.direct_candidates) +
                         " validator-derived=" +
                         std::to_string(stats.derived_candidates) +
                         " duplicates=" +
                         std::to_string(stats.duplicate_candidates) +
                         " promoted=" +
                         std::to_string(stats.promoted_candidates) +
                         " direct_seen=" +
                         std::to_string(m_live_eq_direct_seen) +
                         " direct_submitted=" +
                         std::to_string(m_live_eq_callback_submitted) +
                         " closure_seen=" +
                         std::to_string(m_live_eq_closure_seen) +
                         " closure_submitted=" +
                         std::to_string(m_live_eq_closure_submitted) +
                         " submitted=" + std::to_string(stats.submitted) +
                         " validator-direct-submitted=" +
                         std::to_string(stats.direct_submitted) +
                         " validator-derived-submitted=" +
                         std::to_string(stats.derived_submitted) +
                         " queue-high-water=" +
                         std::to_string(stats.queue_high_water) +
                         " queue-wait-total=" +
                         util::fmt_duration(stats.queue_wait) +
                         " queue-wait-max=" +
                         util::fmt_duration(stats.max_queue_wait) +
                         " seed-checks=" +
                         std::to_string(stats.seed_checks) +
                         " seed-time=" +
                         util::fmt_duration(stats.seed_time) +
                         " seed-model-count=" +
                         std::to_string(stats.seed_models) +
                         " seed-initial-pruned=" +
                         std::to_string(stats.seed_initial_pruned) +
                         " seed-late-pruned=" +
                         std::to_string(stats.seed_late_pruned) +
                         " validation-model-pruned=" +
                         std::to_string(stats.validation_model_pruned) +
                         " prefinal-batches=" +
                         std::to_string(stats.prefinal_batches) +
                         " final-batches=" +
                         std::to_string(stats.final_batches) +
                         " partial-batches=" +
                         std::to_string(stats.partial_batches) +
                         " regular-batches=" +
                         std::to_string(stats.regular_batches) +
                         " checks=" + std::to_string(stats.checks) +
                         " proved=" + std::to_string(stats.proved) +
                         " refuted=" + std::to_string(stats.refuted) +
                         " unknown=" + std::to_string(stats.unknown) +
                         " model-pruned=" + std::to_string(stats.model_pruned) +
                         " models=" +
                         std::to_string(stats.counterexample_models) +
                         " pending=" + std::to_string(stats.pending) +
                         " applied=" + std::to_string(m_live_eq_applied) +
                         " propagated=" +
                         std::to_string(m_live_eq_propagated) +
                         " applied-search=" +
                         std::to_string(m_live_eq_applied_during_search) +
                         " applied-final=" +
                         std::to_string(m_live_eq_applied_at_final) +
                         " gb-committed=" +
                         std::to_string(m_live_eq_gb_committed) +
                         " gb-pending=" +
                         std::to_string(gb_pending) +
                         " gb-flushes=" +
                         std::to_string(m_live_eq_gb_flushes) +
                         " gb-pending-high-water=" +
                         std::to_string(m_live_eq_gb_pending_high_water) +
                         " empty-drains-avoided=" +
                         std::to_string(m_live_eq_empty_drains_avoided) +
                         " final-waves=" +
                         std::to_string(m_live_eq_final_waves) +
                         " final-waits=" +
                         std::to_string(m_live_eq_final_waits) +
                         " final-wait-time=" +
                         util::fmt_duration(m_live_eq_final_wait_time) +
                         " check-time=" + util::fmt_duration(stats.check_time));
        }
        LOG_INFO(g_log, "singular", "eqmod summary: " +
                                         terminal_eqmod_summary());
        LOG_INFO(g_log, "singular",
                 "eqmod paths: all-false-conflicts=" +
                     std::to_string(m_eqmod_all_false_conflicts) +
                     " unit-conflicts=" +
                     std::to_string(m_eqmod_unit_conflicts) +
                     " mixed-conflicts=" +
                     std::to_string(m_eqmod_mixed_conflicts) +
                     " true-lemma-propagations=" +
                     std::to_string(m_eqmod_true_lemma_propagations) +
                     " true-lemma-conflicts=" +
                     std::to_string(m_eqmod_true_lemma_conflicts) +
                     " propagated-assignment-conflicts=" +
                     std::to_string(m_eqmod_propagated_assignment_conflicts) +
                     " membership-batches=" +
                     std::to_string(m_eqmod_membership_batch_calls) +
                     " batch-groups=" +
                     std::to_string(m_eqmod_membership_batch_groups) +
                     " batch-targets=" +
                     std::to_string(m_eqmod_membership_batch_targets) +
                     " deferred-refutation-checks=" +
                     std::to_string(m_deferred_eqmod_refutation_checks) +
                     " true-lemma-cache-hits=" +
                     std::to_string(m_eqmod_true_lemma_cache_hits) +
                     " true-lemma-cache-misses=" +
                     std::to_string(m_eqmod_true_lemma_cache_misses) +
                     " p1-prime-product-queries=" +
                     std::to_string(m_eqmod_p1_product_queries) +
                     " p1-prime-product-members=" +
                     std::to_string(m_eqmod_p1_product_members) +
                     " p1-prime-product-nonmembers=" +
                     std::to_string(m_eqmod_p1_product_nonmembers) +
                     " p1-prime-product-cache-hits=" +
                     std::to_string(m_eqmod_p1_product_cache_hits) +
                     " p1-prime-product-conflicts=" +
                     std::to_string(m_eqmod_p1_product_conflicts));
        for (unsigned family = 1; family <= 4; ++family)
            for (const auto &[reason, count] :
                 m_eqmod_validation_skip_reasons[family])
                LOG_INFO(g_log, "singular",
                         "eqmod validation skip: P" +
                             std::to_string(family) + " reason=" + reason +
                             " count=" + std::to_string(count));
        std::cout << "===== [final] =====\n";
    }

    user_propagator_base *fresh(context &nctx) override
    {
        return new PolyPropagator(nctx, m_env, m_cmap, m_indet_ring_names, m_ring_vars,
                                  m_qvar_names, m_eqmodn_qvar_names,
                                  m_eqmodp1_atoms, m_eqmodn_atoms,
                                  m_eq_callback_options,
                                  m_all_bv_terms, m_eq_coeff_views, m_online_bv_constraints,
                                  m_online_bv_terms,
                                  m_partition_prepass_equalities,
                                  m_partition_prepass_triggers);
    }

    std::string terminal_eqmod_summary() const
    {
        return render_summary(g_cli.enable_final_fixed_value_check);
    }
};

int main(int argc, char **argv)
{
    cli::ParseResult parsed = cli::parse_options(argc, argv);
    if (parsed.selftest)
        return run_rewrite_selftests();

    std::ofstream runlog("run.log", std::ios::out | std::ios::trunc);
    if (!runlog.is_open())
    {
        std::cerr << "Error: cannot open run.log for writing\n";
        return 1;
    }

    std::ostream terminal_out(std::cout.rdbuf());

    try
    {
        if (!parsed.ok)
        {
            if (!parsed.missing_input && !parsed.error.empty())
                std::cerr << parsed.error << "\n";
            if (parsed.show_usage)
                cli::print_usage(std::cerr, argv[0]);

            if (parsed.missing_input)
                runlog << "Usage requested: missing input file\n";
            else if (parsed.log_error)
                runlog << parsed.error << "\n";
            return 1;
        }

        g_cli = std::move(parsed.options);
        if (g_cli.no_trace)
            g_log.set_global(util::LogLevel::Debug);
        util::singular::configure_dump({g_cli.dump_singular, "logs/singular", &g_log});

        cli::report::Summary summary;
        summary.input_file = g_cli.input_file;
        summary.options = g_cli.option_summary;
        std::string terminal_model;

        g_groebner_timing.reset();
        g_final_fixed_value_check_timing.reset();
        g_final_fixed_value_check_span_start.reset();
        util::singular::reset_runtime_statistics();

        const auto total_t0 = clk::now();
        cli::report::print_input_section(
            terminal_out, summary.input_file, summary.options);

        {
            cli::report::ScopedStreamRedirect redirect_cout(
                std::cout, runlog.rdbuf());
            cli::report::ScopedStreamRedirect redirect_cerr(
                std::cerr, runlog.rdbuf());

            LOG_TRACE(g_log, "parse", "Reading SMT2 file: " + g_cli.input_file);
            LOG_INFO(g_log, "parse", "Reading SMT2 file: " + g_cli.input_file);

            context c;

            cli::report::begin_timed_row(terminal_out, "Parsing SMT2 file:");
            auto parse_t0 = clk::now();
            std::vector<expr> asserts =
                smt2::load_assertions(c, g_cli.input_file);
            auto parse_t1 = clk::now();
            summary.parse_time = std::chrono::duration_cast<std::chrono::nanoseconds>(parse_t1 - parse_t0);
            cli::report::finish_timed_row(
                terminal_out, "OK", summary.parse_time);

            LOG_TRACE(g_log, "parse", "Loaded " + std::to_string(asserts.size()) + " assertions.");

            util::autozero::Result auto_zero_lemma_result;
            if (g_cli.enable_auto_zero_lemmas ||
                g_cli.enable_auto_zero_lemmas_bv1_callback)
            {
                cli::report::begin_timed_row(
                    terminal_out, "Auto-zero-lemma discovery:");
                const auto auto_zero_lemma_t0 = clk::now();
                auto_zero_lemma_result =
                    util::autozero::discover_implied_zeros(
                        c, asserts,
                        g_cli.enable_auto_zero_lemmas_bv1_callback
                            ? util::autozero::DiscoveryMode::Callback
                            : util::autozero::DiscoveryMode::GroupedZeroAnchor,
                        g_log);
                cli::report::finish_timed_row(
                    terminal_out, "OK",
                    std::chrono::duration_cast<std::chrono::nanoseconds>(
                        clk::now() - auto_zero_lemma_t0));
            }

            if (!g_cli.inject_ideal_eq.empty())
            {
                for (const auto &[a, b] : g_cli.inject_ideal_eq)
                    LOG_INFO(g_log, "inject",
                             "[inject-ideal-eq] will inject " + a + " - " + b +
                                 " into ideal during GB");
            }

            // Live mode is intentionally independent from the seeded BV
            // equality prepass. Candidates come only from Main Solver equality
            // callbacks. Workers start during search once a full batch exists;
            // final() releases every partial tail batch.
            const bool enable_bv_eq_prepass = g_cli.enable_eq_gb_z3;
            util::bveq::Result bv_eq_result;
            if (enable_bv_eq_prepass)
            {
                cli::report::begin_timed_row(
                    terminal_out, "BV equality prover:");
                auto bveq_t0 = clk::now();
                util::bveq::Options bv_eq_options;
                bv_eq_options.parallel_candidates = g_cli.enable_eq_gb_z3_parallel_candidates;
                bv_eq_options.all_bv_constants = g_cli.enable_eq_gb_z3_all_bv_constants;
                bv_eq_options.enable_fallback = g_cli.enable_bv_eq_fallback;
                bv_eq_options.validation_batch_size = g_cli.eq_gb_z3_validation_batch_size;
                bv_eq_options.seeded_candidate_solvers = g_cli.eq_gb_z3_seeded_candidate_solvers;
                bv_eq_result = util::bveq::prove(c, asserts, bv_eq_options, g_log);
                LOG_INFO(g_log, "eqgb",
                         "stored " +
                             std::to_string(bv_eq_result.equalities.size()) +
                             " globally proved BV equality fact(s)");
                auto bveq_t1 = clk::now();
                auto bveq_time = std::chrono::duration_cast<std::chrono::nanoseconds>(bveq_t1 - bveq_t0);
                cli::report::finish_timed_row(
                    terminal_out, "OK", bveq_time);
            }

            if (g_cli.enable_eq_gb_z3)
            {
                std::vector<expr> injected_eqps =
                    util::bveq::inject_as_eqp(c, asserts, bv_eq_result, g_log);
                asserts.insert(asserts.end(), injected_eqps.begin(), injected_eqps.end());
            }

            util::eqpartition::PrepassResult partition_prepass;
            if (g_cli.enable_eq_gb_partition_prepass)
            {
                cli::report::begin_timed_row(
                    terminal_out, "Partition equality prepass:");
                const auto partition_prepass_t0 = clk::now();
                const auto prepass_options =
                    solver_options::make_partition_prepass_options(g_cli);
                if (!prepass_options)
                    partition_prepass = util::eqpartition::run_eqp_prepass(
                        c, asserts, &g_log);
                else
                    partition_prepass = util::eqpartition::run_eqp_prepass(
                        c, asserts, *prepass_options, &g_log);
                if (partition_prepass.status ==
                    util::eqpartition::Status::Complete)
                    asserts.insert(
                        asserts.end(),
                        partition_prepass.assertions.begin(),
                        partition_prepass.assertions.end());
                cli::report::finish_timed_row(
                    terminal_out,
                    partition_prepass.status ==
                            util::eqpartition::Status::Complete
                        ? "OK"
                        : "INCOMPLETE",
                    std::chrono::duration_cast<std::chrono::nanoseconds>(
                        clk::now() - partition_prepass_t0));
                if (g_cli.eq_gb_partition_prepass_bv1_zero_only)
                {
                    terminal_out
                        << "BV1 zero-only result: candidates="
                        << partition_prepass.bv1_zero_candidates
                        << " checks=" << partition_prepass.bv1_zero_checks
                        << " proved=" << partition_prepass.bv1_zero_proved
                        << " refuted=" << partition_prepass.bv1_zero_refuted
                        << " unknown=" << partition_prepass.bv1_zero_unknown
                        << " time="
                        << util::fmt_duration(
                               partition_prepass.bv1_zero_elapsed)
                        << "\n";
                    terminal_out.flush();
                    runlog.flush();
                    return 0;
                }
            }

            if (g_cli.enable_auto_zero_lemmas ||
                g_cli.enable_auto_zero_lemmas_bv1_callback)
            {
                std::vector<expr> auto_zero_eqps =
                    util::autozero::inject_as_eqp(
                        c, asserts, auto_zero_lemma_result, g_log);
                asserts.insert(asserts.end(), auto_zero_eqps.begin(),
                               auto_zero_eqps.end());
            }

            std::vector<expr> online_bv_constraints;
            std::vector<expr> online_bv_terms;
            if (eq_gb_generator_mode_enabled())
            {
                for (const expr &assertion : asserts)
                    if (!util::bveq::assertion_contains_poly(assertion))
                        online_bv_constraints.push_back(assertion);
                std::unordered_set<Z3_ast> online_base_set;
                for (const expr &assertion : asserts)
                    collect_coeff_bases_rec(assertion, online_base_set);
                std::unordered_set<Z3_ast> online_term_set;
                for (Z3_ast ast : online_base_set)
                {
                    expr base(c, ast);
                    if (!is_bv_to_int_app(base))
                        continue;
                    expr term = base.arg(0);
                    if (term.is_const() && !term.is_numeral() &&
                        online_term_set.insert((Z3_ast)term).second)
                        online_bv_terms.push_back(term);
                }
            }

            std::vector<expr> pre_rewrite_coeff_bases;
            if (rewrite_aware_coeff_views_enabled())
            {
                std::unordered_set<Z3_ast> pre_base_set;
                for (const expr &f : asserts)
                    collect_coeff_bases_rec(f, pre_base_set);
                pre_rewrite_coeff_bases.reserve(pre_base_set.size());
                for (Z3_ast ast : pre_base_set)
                {
                    expr base(c, ast);
                    if (eq_gb_generator_mode_enabled())
                        pre_rewrite_coeff_bases.push_back(base);
                }
                std::sort(pre_rewrite_coeff_bases.begin(), pre_rewrite_coeff_bases.end(),
                          [](const expr &x, const expr &y) { return x.to_string() < y.to_string(); });
            }
            RewriteOptions rwopt;
            rwopt.enable_rewriting = g_cli.enable_rewriting;
            rwopt.use_singular_normalization = g_cli.enable_rewrite_singular_nf;
            rwopt.enable_moduli_normalization = g_cli.enable_moduli_normalization;
            rwopt.use_subexpression_rules = g_cli.enable_subexpression_rules;
            rwopt.use_raw_poly_power_rules = g_cli.enable_raw_poly_power_rules;
            rwopt.preserve_eqmodp1_vars = g_cli.preserve_eqmodp1_vars;
            rwopt.enable_expression_growth_check = g_cli.enable_expression_growth_check;
            rwopt.disable_rewrite_cache = g_cli.disable_rewrite_cache;
            rwopt.verify_rewrite_lookups = g_cli.verify_rewrite_lookups;

            std::ofstream rewrite_log;
            if (g_cli.rewrite_log_requested)
            {
                rewrite_log.open("rewrite.log", std::ios::out | std::ios::trunc);
                if (!rewrite_log.is_open())
                    throw std::runtime_error("cannot open rewrite.log for writing");
                rwopt.rewrite_log = &rewrite_log;
            }
            std::ofstream rewrite_lookup_log;
            if (g_cli.verify_rewrite_lookups)
            {
                rewrite_lookup_log.open("rewritelookups.log", std::ios::out | std::ios::trunc);
                if (!rewrite_lookup_log.is_open())
                    throw std::runtime_error("cannot open rewritelookups.log for writing");
                rwopt.rewrite_lookup_log = &rewrite_lookup_log;
            }

            cli::report::begin_timed_row(
                terminal_out, "Rewriting assignments:");
            auto rewrite_t0 = clk::now();
            RewriteResult rr = run_rewriting_pipeline(c, asserts, rwopt, g_log);
            auto rewrite_t1 = clk::now();
            summary.rewrite_time = std::chrono::duration_cast<std::chrono::nanoseconds>(rewrite_t1 - rewrite_t0);
            asserts = std::move(rr.asserts);
            std::vector<RewrittenCoeffBase> eq_coeff_views;
            if (rewrite_aware_coeff_views_enabled())
                eq_coeff_views = rewrite_coeff_bases_to_int(pre_rewrite_coeff_bases, rr.rules_used);
            cli::report::finish_timed_row(
                terminal_out, "OK", summary.rewrite_time);

            solver s(c);

            for (size_t i = 0; i < asserts.size(); ++i)
            {
                std::string nm = "A#" + std::to_string(i);
                expr tag = c.bool_const(nm.c_str());

                Z3_solver_assert_and_track(
                    (Z3_context)c,
                    (Z3_solver)s,
                    (Z3_ast)asserts[i],
                    (Z3_ast)tag);
            }

            std::vector<expr> partition_prepass_triggers;
            if (g_cli.eq_gb_partition_prepass_propagation &&
                !partition_prepass.native_equalities.empty())
            {
                expr trigger(
                    c, Z3_mk_fresh_const(
                           (Z3_context)c,
                           "eq_gb_partition_prepass_trigger",
                           (Z3_sort)c.bool_sort()));
                s.add(trigger);
                partition_prepass_triggers.push_back(trigger);
                LOG_INFO(g_log, "eqpartition",
                         "partition prepass propagation armed: equalities=" +
                             std::to_string(
                                 partition_prepass.native_equalities.size()) +
                             " trigger=" + trigger.to_string());
            }

            std::vector<expr> eqps;
            for (auto &f : asserts)
                collect_eqP_rec(f, eqps);
            eqps = dedup_and_drop_trivial_eqp(eqps);

            std::vector<expr> lhs, rhs;
            lhs.reserve(eqps.size());
            rhs.reserve(eqps.size());
            for (size_t i = 0; i < eqps.size(); ++i)
            {
                LOG_TRACE(g_log, "parse", "Found eqP#" + std::to_string(i) + " constraint: " + eqps[i].to_string());
                lhs.push_back(eqps[i].arg(0));
                rhs.push_back(eqps[i].arg(1));
            }

            std::vector<expr> eqmodsP1;
            for (auto &f : asserts)
                collect_eqmod_rec(f, 1, eqmodsP1);

            for (size_t i = 0; i < eqmodsP1.size(); ++i)
            {
                LOG_TRACE(g_log, "parse",
                          "Found eqmodP1#" + std::to_string(i) +
                              " constraint: " + eqmodsP1[i].to_string());
            }

            std::vector<std::vector<expr>> eqmodn_atoms(5);
            for (unsigned arity = 2; arity <= 4; ++arity)
            {
                for (auto &f : asserts)
                    collect_eqmod_rec(f, arity, eqmodn_atoms[arity]);
                for (size_t i = 0; i < eqmodn_atoms[arity].size(); ++i)
                    LOG_TRACE(g_log, "parse",
                              "Found eqmodP" + std::to_string(arity) + "#" +
                                  std::to_string(i) + " constraint: " +
                                  eqmodn_atoms[arity][i].to_string());
            }

            std::vector<std::string> indets = collect_all_indets(asserts);
            std::vector<std::string> poly_symbols = collect_all_raw_poly_symbols(asserts);
            IndetEnv env;
            env.names = indets;
            env.split_indet_count = (unsigned)indets.size();
            for (unsigned i = 0; i < indets.size(); ++i)
                env.idx["PVar:" + indets[i]] = i;
            for (const std::string &symbol : poly_symbols)
            {
                unsigned i = (unsigned)env.names.size();
                env.names.push_back(symbol);
                env.idx["PolySymbol:" + symbol] = i;
            }

            std::unordered_set<Z3_ast> baseS;
            for (auto &f : asserts)
                collect_coeff_bases_rec(f, baseS);
            if (rewrite_aware_coeff_views_enabled())
                for (const RewrittenCoeffBase &view : eq_coeff_views)
                    collect_coeff_bases_rec(view.rewritten_int, baseS);

            std::vector<z3::expr> bases;
            bases.reserve(baseS.size());
            for (auto a : baseS)
                bases.emplace_back(c, a);

            std::sort(bases.begin(), bases.end(),
                      [](const z3::expr &x, const z3::expr &y)
                      { return x.to_string() < y.to_string(); });

            std::unordered_set<Z3_ast> all_bv_set;
            for (const expr &f : asserts)
                util::bveq::collect_bv_constants(f, all_bv_set);
            std::vector<expr> all_bv_terms;
            all_bv_terms.reserve(all_bv_set.size());
            for (Z3_ast ast : all_bv_set)
                all_bv_terms.emplace_back(c, ast);
            std::sort(all_bv_terms.begin(), all_bv_terms.end(),
                      [](const expr &x, const expr &y) { return x.to_string() < y.to_string(); });

            std::unordered_set<std::string> used;

            CoeffVarMap cmap;
            cmap.z3_bases = bases;
            cmap.ring_names.resize(bases.size());

            for (size_t i = 0; i < bases.size(); ++i)
            {
                std::string base_name = coeff_base_pretty_name(bases[i]);
                std::string base = sanitize_ring_var_base(base_name);
                cmap.ring_names[i] = make_unique_name(base, used);
            }

            cmap.base_to_index.clear();
            for (size_t i = 0; i < bases.size(); ++i)
                cmap.base_to_index[(Z3_ast)bases[i]] = (unsigned)i;

            if (rewrite_aware_coeff_views_enabled())
            {
                std::vector<RewrittenCoeffBase> lowerable_views;
                lowerable_views.reserve(eq_coeff_views.size());
                std::size_t skipped_views = 0;
                for (const RewrittenCoeffBase &view : eq_coeff_views)
                {
                    std::unordered_set<Z3_ast> dependencies;
                    collect_coeff_bases_rec(view.rewritten_int, dependencies);
                    bool lowerable = true;
                    for (Z3_ast dependency : dependencies)
                    {
                        if (cmap.base_to_index.count(dependency) == 0)
                        {
                            lowerable = false;
                            break;
                        }
                    }
                    if (lowerable)
                        lowerable_views.push_back(view);
                    else
                        ++skipped_views;
                }
                eq_coeff_views = std::move(lowerable_views);
                LOG_INFO(g_log, "eqgb",
                         "rewrite-aware coefficient views=" +
                             std::to_string(eq_coeff_views.size()) +
                             " skipped_nonlowerable=" + std::to_string(skipped_views));
            }

            std::vector<std::string> indet_ring_names(env.names.size());
            for (size_t i = 0; i < env.names.size(); ++i)
            {
                const bool is_poly_symbol = i >= env.split_indet_count;
                std::string prefix = is_poly_symbol ? "poly_" : "";
                std::string base = sanitize_ring_var_base(prefix + env.names[i]);
                indet_ring_names[i] = make_unique_name(base, used);
            }

            std::vector<std::string> pvar_ring_names(
                indet_ring_names.begin(),
                indet_ring_names.begin() + env.split_indet_count);
            std::vector<std::string> poly_symbol_ring_names(
                indet_ring_names.begin() + env.split_indet_count,
                indet_ring_names.end());

            std::vector<std::string> qvar_names(eqmodsP1.size());
            for (size_t i = 0; i < eqmodsP1.size(); ++i)
            {
                qvar_names[i] = make_unique_name("u_mod_0_" + std::to_string(i), used);
            }

            std::vector<std::vector<std::vector<std::string>>> eqmodn_qvar_names(5);
            for (unsigned arity = 2; arity <= 4; ++arity)
            {
                eqmodn_qvar_names[arity].resize(eqmodn_atoms[arity].size());
                for (size_t i = 0; i < eqmodn_atoms[arity].size(); ++i)
                    for (unsigned modulus = 0; modulus < arity; ++modulus)
                        eqmodn_qvar_names[arity][i].push_back(make_unique_name(
                            "u_mod_" + std::to_string(arity - 1) + "_" +
                                std::to_string(i) + "_" + std::to_string(modulus),
                            used));
            }

            std::vector<std::string> ring_vars;
            if (g_cli.use_groebner_ring_var_order)
            {
                ring_vars = build_groebner_ring_var_order(cmap.ring_names, poly_symbol_ring_names,
                                                          pvar_ring_names,
                                                          qvar_names, eqmodn_qvar_names);
            }
            else
            {
                ring_vars.reserve(cmap.ring_names.size() + indet_ring_names.size() +
                                  qvar_names.size());
                for (unsigned arity = 4; arity >= 2; --arity)
                    for (auto atom = eqmodn_qvar_names[arity].rbegin();
                         atom != eqmodn_qvar_names[arity].rend(); ++atom)
                        ring_vars.insert(ring_vars.end(), atom->begin(), atom->end());
                for (auto atom = qvar_names.rbegin(); atom != qvar_names.rend(); ++atom)
                    ring_vars.push_back(*atom);
                ring_vars.insert(ring_vars.end(), poly_symbol_ring_names.begin(), poly_symbol_ring_names.end());
                ring_vars.insert(ring_vars.end(), cmap.ring_names.begin(), cmap.ring_names.end());
                ring_vars.insert(ring_vars.end(), pvar_ring_names.begin(), pvar_ring_names.end());
            }

            const std::size_t p1_qvars = qvar_names.size();
            std::array<std::size_t, 5> family_qvars{};
            family_qvars[1] = p1_qvars;
            for (unsigned arity = 2; arity <= 4; ++arity)
                for (const auto &atom_qvars : eqmodn_qvar_names[arity])
                    family_qvars[arity] += atom_qvars.size();
            const std::size_t auxiliary_count =
                std::count_if(cmap.ring_names.begin(), cmap.ring_names.end(),
                              is_groebner_aux_var);
            const std::size_t coefficient_count =
                cmap.ring_names.size() - auxiliary_count;
            const std::size_t singular_ring_var_limit =
                util::singular::ring_variable_limit();

            LOG_INFO(
                g_log, "init",
                "eqmod ring preflight: P1 atoms=" +
                    std::to_string(eqmodsP1.size()) + " qvars=" +
                    std::to_string(family_qvars[1]) + " ; P2 atoms=" +
                    std::to_string(eqmodn_atoms[2].size()) + " qvars=" +
                    std::to_string(family_qvars[2]) + " ; P3 atoms=" +
                    std::to_string(eqmodn_atoms[3].size()) + " qvars=" +
                    std::to_string(family_qvars[3]) + " ; P4 atoms=" +
                    std::to_string(eqmodn_atoms[4].size()) + " qvars=" +
                    std::to_string(family_qvars[4]) + " ; raw-poly=" +
                    std::to_string(poly_symbol_ring_names.size()) +
                    " auxiliary=" + std::to_string(auxiliary_count) +
                    " coefficients=" + std::to_string(coefficient_count) +
                    " PVar=" + std::to_string(pvar_ring_names.size()) +
                    " total=" + std::to_string(ring_vars.size()) +
                    " Singular-ABI-limit=" +
                    std::to_string(singular_ring_var_limit));
            util::singular::require_ring_variable_capacity(ring_vars.size());

            LOG_TRACE(g_log, "init",
                      "Initializing propagator with " +
                          std::to_string(eqps.size()) + " eqP constraint(s), " +
                          std::to_string(eqmodsP1.size()) + " eqmodP1 constraint(s), " +
                          std::to_string(eqmodn_atoms[2].size()) + " eqmodP2 constraint(s), " +
                          std::to_string(eqmodn_atoms[3].size()) + " eqmodP3 constraint(s), " +
                          std::to_string(eqmodn_atoms[4].size()) + " eqmodP4 constraint(s).");

            PolyPropagator up(&s, eqps, lhs, rhs, eqmodsP1, eqmodn_atoms,
                              env, cmap, indet_ring_names, ring_vars, qvar_names,
                              eqmodn_qvar_names, g_cli.eq_callback_options, all_bv_terms,
                              eq_coeff_views, online_bv_constraints, online_bv_terms,
                              partition_prepass.native_equalities,
                              partition_prepass_triggers);

            cli::report::begin_timed_row(terminal_out, "Solving with Z3:");
            auto solve_t0 = clk::now();
            check_result r = s.check();
            auto solve_t1 = clk::now();
            summary.solve_time = std::chrono::duration_cast<std::chrono::nanoseconds>(solve_t1 - solve_t0);
            summary.result = r;
            cli::report::finish_timed_row(
                terminal_out, "OK", summary.solve_time);

            std::cout << "Solver result: " << r << "\n";
            if (r == unknown)
                std::cout << "Reason unknown: " << s.reason_unknown() << "\n";
            if (SHOW_MODEL && r == sat)
            {
                print_model_filtered(s.get_model());
                if (g_cli.show_model_on_terminal)
                {
                    std::ostringstream model_out;
                    print_model_filtered(s.get_model(), model_out);
                    terminal_model = model_out.str();
                }
            }

            std::cout << "[timer] z3.check() = " << util::fmt_duration(solve_t1 - solve_t0) << "\n";
            std::cout.flush();
            std::cerr.flush();

            summary.groebner_calls = g_groebner_timing.calls;
            summary.groebner_time = g_groebner_timing.elapsed;
            summary.final_fixed_value_check_calls = g_final_fixed_value_check_timing.calls;
            summary.singular_runtime = util::singular::runtime_statistics();
            summary.self_max_rss_kb = util::singular::current_process_max_rss_kb();
            summary.eqmod_summary = up.terminal_eqmod_summary();
            if (g_final_fixed_value_check_span_start)
            {
                summary.final_fixed_value_check_time =
                    std::chrono::duration_cast<std::chrono::nanoseconds>(solve_t1 - *g_final_fixed_value_check_span_start);
            }
            else
            {
                summary.final_fixed_value_check_time = g_final_fixed_value_check_timing.elapsed;
            }
            summary.total_time = std::chrono::duration_cast<std::chrono::nanoseconds>(clk::now() - total_t0);
            runlog.flush();
        }

        cli::report::print_summary(
            terminal_out, summary, terminal_model,
            g_cli.show_model_on_terminal);
        return 0;
    }
    catch (const z3::exception &ex)
    {
        runlog << "Z3 error: " << ex.msg() << "\n";
        runlog.flush();
        std::cerr << "\n";
        std::cerr << "Z3 error: " << ex.msg() << "\n";
        return 1;
    }
    catch (const std::exception &ex)
    {
        runlog << "Error: " << ex.what() << "\n";
        runlog.flush();
        std::cerr << "\n";
        std::cerr << "Error: " << ex.what() << "\n";
        return 1;
    }
}
