#pragma once

#include <z3++.h>
#include <Singular/libsingular.h>
#include <gmpxx.h>

#include <string>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "util/logger.hpp"
#include "util/singular_lowering.hpp"
#include "util/singular_membership_prover.hpp"
#include "util/singular_process_pool.hpp"

namespace eqmod
{

// Lowered representation shared by the runtime EqmodEngine and the
// PolyPropagator callback adapter. Singular polynomial fields are owned by the
// containing engine and must be released with destroy().
struct P1Compiled
{
    z3::expr atom;
    z3::expr A;
    z3::expr B;
    z3::expr Mterm;

    bool modulus_ok = false;
    bool modulus_is_const = false;
    mpz_class m_const = 0;

    poly M_poly = nullptr;
    poly D = nullptr;

    std::string u_name;
    poly U_poly = nullptr;
    poly true_gen = nullptr;
    bool valid = false;
    std::string incomplete_reason;
    Z3_lbool propagated_truth = Z3_L_UNDEF;
    std::vector<z3::expr> propagated_truth_ants;
    std::vector<std::pair<z3::expr, z3::expr>> propagated_truth_eqs;

    ring owner_ring = nullptr;

    P1Compiled(const z3::expr &atom,
               const z3::expr &A,
               const z3::expr &B,
               const z3::expr &modulus,
               std::string quotient_name,
               ring owner_ring);
    ~P1Compiled();
    P1Compiled(const P1Compiled &) = delete;
    P1Compiled &operator=(const P1Compiled &) = delete;
    P1Compiled(P1Compiled &&other) noexcept;
    P1Compiled &operator=(P1Compiled &&other) noexcept;
};

struct NCompiled
{
    z3::expr atom;
    z3::expr A;
    z3::expr B;
    unsigned arity = 0;
    std::vector<z3::expr> modulus_terms;
    std::vector<poly> modulus_polys;
    std::vector<std::string> quotient_names;
    std::vector<poly> quotient_polys;

    // Compatibility views retained while the mature P2 inference path is
    // folded into the arity-independent engine implementation.
    z3::expr M1term;
    z3::expr M2term;

    poly D = nullptr;
    poly M1_poly = nullptr;
    poly M2_poly = nullptr;

    std::string u1_name;
    std::string u2_name;
    poly U1_poly = nullptr;
    poly U2_poly = nullptr;
    poly true_gen = nullptr;
    bool valid = false;
    std::string incomplete_reason;
    Z3_lbool propagated_truth = Z3_L_UNDEF;
    std::vector<z3::expr> propagated_truth_ants;
    std::vector<std::pair<z3::expr, z3::expr>> propagated_truth_eqs;

    ring owner_ring = nullptr;

    NCompiled(const z3::expr &atom,
              const z3::expr &A,
              const z3::expr &B,
              unsigned arity,
              std::vector<z3::expr> modulus_terms,
              std::vector<std::string> quotient_names,
              ring owner_ring);
    ~NCompiled();
    NCompiled(const NCompiled &) = delete;
    NCompiled &operator=(const NCompiled &) = delete;
    NCompiled(NCompiled &&other) noexcept;
    NCompiled &operator=(NCompiled &&other) noexcept;
};

using P2Compiled = NCompiled;

class EqmodEngine
{
protected:
    struct ProofPremises
    {
        std::vector<z3::expr> fixed;
        std::vector<std::pair<z3::expr, z3::expr>> equalities;
    };

    struct CachedTrueLemmaMembership
    {
        bool member = false;
        ProofPremises premises;
    };

    struct SourceGenerator
    {
        poly gen = nullptr;
        std::optional<z3::expr> source_atom;
        std::optional<std::pair<z3::expr, z3::expr>> source_eq;
        ring owner_ring = nullptr;

        SourceGenerator(poly generator,
                        std::optional<z3::expr> atom,
                        std::optional<std::pair<z3::expr, z3::expr>> equality,
                        ring owner_ring);
        ~SourceGenerator();
        SourceGenerator(const SourceGenerator &) = delete;
        SourceGenerator &operator=(const SourceGenerator &) = delete;
        SourceGenerator(SourceGenerator &&other) noexcept;
        SourceGenerator &operator=(SourceGenerator &&other) noexcept;
    };

    std::vector<std::string> m_qvar_names;
    std::vector<std::vector<std::vector<std::string>>>
        m_eqmodn_qvar_names;
    std::vector<z3::expr> m_eqmodp1_atoms;
    std::unordered_map<Z3_ast, std::size_t> m_eqmodp1_slots;
    std::vector<std::vector<z3::expr>> m_eqmodn_atoms;
    std::vector<std::unordered_map<Z3_ast, std::size_t>> m_eqmodn_slots;

    std::vector<P1Compiled> m_eqmodp;
    std::vector<P2Compiled> m_eqmodp2;
    std::vector<NCompiled> m_eqmodp3;
    std::vector<NCompiled> m_eqmodp4;
    std::unordered_set<Z3_ast> m_compiled_eqmod_atoms;

    std::size_t m_last_eqmod_true_lemma_eq_generator_epoch =
        static_cast<std::size_t>(-1);
    std::string m_last_eqmod_true_lemma_source_signature;
    std::size_t m_last_eqmod_true_lemma_true_count =
        static_cast<std::size_t>(-1);
    std::size_t m_last_eqmod_true_lemma_p1_count =
        static_cast<std::size_t>(-1);
    std::size_t m_last_eqmod_true_lemma_p2_count =
        static_cast<std::size_t>(-1);
    std::size_t m_last_eqmod_true_lemma_p3_count =
        static_cast<std::size_t>(-1);
    std::size_t m_last_eqmod_true_lemma_p4_count =
        static_cast<std::size_t>(-1);
    std::string m_pending_eqmod_true_lemma_source_signature;
    std::size_t m_pending_eqmod_true_lemma_source_updates = 0;
    std::size_t m_deferred_eqmod_true_lemma_checks = 0;
    bool m_eqmod_true_lemma_replay_needed = false;
    std::unordered_map<
        std::string,
        std::unordered_map<Z3_ast, CachedTrueLemmaMembership>>
        m_eqmod_true_lemma_membership_cache;
    std::size_t m_eqmod_true_lemma_cache_hits = 0;
    std::size_t m_eqmod_true_lemma_cache_misses = 0;
    std::vector<std::size_t> m_eqmod_true_lemma_cache_hits_by_family =
        std::vector<std::size_t>(5, 0);
    std::vector<std::size_t> m_eqmod_true_lemma_cache_misses_by_family =
        std::vector<std::size_t>(5, 0);
    std::unordered_set<std::string> m_eqmod_unit_nonmember_cache;
    std::unordered_map<std::string, std::unordered_set<Z3_ast>>
        m_eqmod_refutation_nonmember_cache;
    std::unordered_set<std::string> m_eqmod_p1_product_nonmember_cache;
    std::unordered_set<std::string> m_eqmod_p1_product_member_cache;
    std::size_t m_eqmod_p1_product_queries = 0;
    std::size_t m_eqmod_p1_product_members = 0;
    std::size_t m_eqmod_p1_product_nonmembers = 0;
    std::size_t m_eqmod_p1_product_cache_hits = 0;
    std::size_t m_eqmod_p1_product_conflicts = 0;
    std::vector<std::size_t> m_eqmod_refutation_cache_hits_by_family =
        std::vector<std::size_t>(5, 0);
    std::vector<std::size_t> m_eqmod_refutation_cache_misses_by_family =
        std::vector<std::size_t>(5, 0);
    std::vector<std::size_t> m_eqmod_refutation_conflicts_by_family =
        std::vector<std::size_t>(5, 0);
    std::string m_last_eqmod_refutation_false_signature;
    std::size_t m_deferred_eqmod_refutation_checks = 0;
    std::vector<std::size_t> m_eqmod_membership_queries =
        std::vector<std::size_t>(5, 0);
    std::vector<std::size_t> m_eqmod_membership_members =
        std::vector<std::size_t>(5, 0);
    std::vector<std::size_t> m_eqmod_membership_nonmembers =
        std::vector<std::size_t>(5, 0);
    std::vector<std::size_t> m_eqmod_validation_checked =
        std::vector<std::size_t>(5, 0);
    std::vector<std::size_t> m_eqmod_validation_skipped =
        std::vector<std::size_t>(5, 0);
    std::vector<std::size_t> m_eqmod_validation_matched =
        std::vector<std::size_t>(5, 0);
    std::vector<std::size_t> m_eqmod_validation_conflicted =
        std::vector<std::size_t>(5, 0);
    std::vector<std::unordered_map<std::string, std::size_t>>
        m_eqmod_validation_skip_reasons =
            std::vector<std::unordered_map<std::string, std::size_t>>(5);
    std::vector<std::size_t> m_eqmod_collected_atoms =
        std::vector<std::size_t>(5, 0);
    std::vector<std::size_t> m_eqmod_invalid_atoms =
        std::vector<std::size_t>(5, 0);
    std::vector<std::vector<std::string>> m_eqmod_incomplete_reasons =
        std::vector<std::vector<std::string>>(5);
    bool m_semantic_validation_incomplete = false;
    std::size_t m_eqmod_all_false_conflicts = 0;
    std::size_t m_eqmod_unit_conflicts = 0;
    std::size_t m_eqmod_mixed_conflicts = 0;
    std::size_t m_eqmod_true_lemma_propagations = 0;
    std::size_t m_eqmod_true_lemma_conflicts = 0;
    std::size_t m_eqmod_propagated_assignment_conflicts = 0;
    std::size_t m_eqmod_membership_batch_calls = 0;
    std::size_t m_eqmod_membership_batch_groups = 0;
    std::size_t m_eqmod_membership_batch_targets = 0;

    EqmodEngine(
        const std::vector<std::string> &p1_qvars,
        const std::vector<std::vector<std::vector<std::string>>> &n_qvars,
        const std::vector<z3::expr> &p1_atoms = {},
        const std::vector<std::vector<z3::expr>> &n_atoms = {});

    void bind_ring(ring current_ring);
    void release();
    void reset_after_pop(bool live_equality_enabled);
    void record_membership(unsigned family, bool member);
    static bool same_poly(poly lhs, poly rhs, ring current_ring);
    std::string render_summary(bool final_validation_enabled) const;
    bool is_compiled(const z3::expr &atom) const;
    void register_slot(const z3::expr &atom, unsigned family,
                       std::size_t index);
    std::size_t require_slot(const z3::expr &atom, unsigned family,
                             const std::string &origin) const;
    bool lower_atom(
        const z3::expr &atom,
        unsigned family,
        const std::string &label,
        const util::singular::lowering::IndetEnv &indets,
        const std::vector<std::string> &indet_ring_names,
        util::singular::lowering::RingEnv &ring_environment,
        const util::singular::lowering::CoeffVarMap &coefficients,
        int coefficient_count,
        util::Logger &log);
    void delete_source_generators(std::vector<SourceGenerator> &sources) const;
    void add_source_generator(
        std::vector<SourceGenerator> &sources,
        poly generator,
        std::optional<z3::expr> source_atom,
        std::optional<std::pair<z3::expr, z3::expr>> source_equality =
            std::nullopt) const;
    ProofPremises premises_from_source_generators(
        const std::vector<SourceGenerator> &sources,
        const std::vector<std::size_t> *used_indices = nullptr) const;
    bool prove_eqmod_membership(
        const std::vector<SourceGenerator> &sources,
        const std::vector<poly> &extra_generators,
        poly target,
        const std::string &label,
        unsigned family);
    void check_cross_family_eqmod_refutations(bool force = false);
    void propagate_eqmod_true_lemmas_from_context(bool force = false);
    bool final_fixed_value_check_all_eqmods();
    bool conflict_on_propagated_eqmod_truth();
    bool conflict_on_propagated_p1_truth();
    bool conflict_on_propagated_p2_truth();
    bool conflict_on_propagated_n_truth();
    bool propagate_true_lemma_or_conflict(
        const z3::expr &atom,
        Z3_lbool current_value,
        ProofPremises premises,
        const std::string &reason);
    template <typename CompiledAtom>
    bool conflict_on_propagated_family(
        std::vector<CompiledAtom> &atoms, const std::string &kind);
    template <typename CompiledAtom,
              typename SameModuli,
              typename AppendModulusGenerators,
              typename ConflictCheck>
    void propagate_true_lemmas_from_context_impl(
        std::vector<CompiledAtom> &atoms,
        const std::string &kind,
        const std::string &gb_label,
        unsigned family,
        const std::string &source_signature,
        bool cache_enabled,
        SameModuli same_moduli,
        AppendModulusGenerators append_modulus_generators,
        ConflictCheck conflict_check);
    void propagate_eqmodP1_true_lemmas_from_context_impl(
        const std::string &source_signature, bool cache_enabled);
    void propagate_eqmodP2_true_lemmas_from_context_impl(
        const std::string &source_signature, bool cache_enabled);
    void propagate_eqmodN_true_lemmas_from_context_impl(
        std::vector<NCompiled> &atoms,
        const std::string &kind,
        const std::string &source_signature,
        bool cache_enabled);

    virtual bool enable_all_true() const = 0;
    virtual bool enable_all_false() const = 0;
    virtual bool enable_mixed() const = 0;
    virtual bool assume_p1_modulus_prime() const = 0;
    virtual bool reuse_base_basis() const = 0;
    virtual bool preprocess_membership() const = 0;
    virtual bool verify_membership_preprocess() const = 0;
    virtual bool enable_ideal_rewrite() const = 0;
    virtual bool enable_true_lemmas() const = 0;
    virtual bool enable_true_lemma_lift_antecedents() const = 0;
    virtual bool enable_true_lemma_cache() const = 0;
    virtual std::size_t refutation_processes() const = 0;
    virtual std::size_t true_lemma_processes() const = 0;
    virtual util::Logger &engine_log() = 0;
    virtual ring engine_ring() const = 0;
    virtual Z3_lbool lbool_of(const z3::expr &atom) const = 0;
    virtual std::string true_context_source_signature() const = 0;
    virtual std::size_t true_context_atom_count() const = 0;
    virtual std::size_t equality_generator_epoch() const = 0;
    virtual bool all_eqp_fixed() const = 0;
    virtual void collect_true_context_source_generators(
        std::vector<SourceGenerator> &sources) = 0;
    virtual util::singular::MembershipGroupBatchResult run_membership_groups(
        const std::vector<poly> &base,
        const std::vector<util::singular::MembershipGroup> &groups,
        std::size_t processes,
        bool return_normal_forms) = 0;
    virtual void accumulate_membership_group_timing(
        const util::singular::MembershipGroupBatchResult &batch) = 0;
    virtual void accumulate_direct_membership_timing(
        const util::singular::GroebnerTiming &timing) = 0;
    virtual void conflict_with(const ProofPremises &premises) = 0;
    virtual void propagate_true_atom(
        const z3::expr &atom, const ProofPremises &premises) = 0;
    virtual void trace_true_lemma_gb(
        bool begin,
        const std::string &label,
        std::size_t equality_generator_count,
        std::size_t total_generator_count) = 0;
    virtual bool build_validation_assignments(
        const z3::expr &A,
        const z3::expr &B,
        const std::vector<z3::expr> &modulus_terms,
        std::vector<poly> &assignments,
        std::string &skip_reason) = 0;
    virtual ProofPremises validation_conflict_premises(
        const z3::expr &atom,
        const z3::expr &A,
        const z3::expr &B,
        const std::vector<z3::expr> &modulus_terms) const = 0;
    virtual std::string label_of(const z3::expr &atom) const = 0;

public:
    virtual ~EqmodEngine();

private:
    ring m_owned_ring = nullptr;
};

poly make_var_poly(util::singular::lowering::RingEnv &environment,
                   const std::string &name);

P1Compiled compile_p1(
    const z3::expr &atom,
    const z3::expr &A,
    const z3::expr &B,
    const z3::expr &modulus,
    const std::string &label,
    const util::singular::lowering::IndetEnv &indets,
    const std::vector<std::string> &indet_ring_names,
    util::singular::lowering::RingEnv &ring_environment,
    const util::singular::lowering::CoeffVarMap &coefficients,
    int coefficient_count,
    const std::string &quotient_name,
    util::Logger &log);

NCompiled compile_n(
    const z3::expr &atom,
    const std::string &label,
    const util::singular::lowering::IndetEnv &indets,
    const std::vector<std::string> &indet_ring_names,
    util::singular::lowering::RingEnv &ring_environment,
    const util::singular::lowering::CoeffVarMap &coefficients,
    int coefficient_count,
    const std::vector<std::string> &quotient_names,
    util::Logger &log);

void destroy(P1Compiled &atom, ring current_ring);
void destroy(NCompiled &atom, ring current_ring);

} // namespace eqmod
