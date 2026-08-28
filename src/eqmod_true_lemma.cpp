#include "eqmod_engine.hpp"

#include <algorithm>
#include <stdexcept>

#include "util/singular_lift_prover.hpp"
#include "util/singular_poly.hpp"

using namespace z3;

namespace eqmod
{

bool EqmodEngine::propagate_true_lemma_or_conflict(
    const expr &atom,
    Z3_lbool current_value,
    ProofPremises premises,
    const std::string &reason)
{
    if (current_value == Z3_L_TRUE)
        return false;
    if (current_value == Z3_L_FALSE)
    {
        ++m_eqmod_true_lemma_conflicts;
        premises.fixed.push_back(atom);
        LOG_INFO(engine_log(), "singular",
                 reason + "; conflicting with FALSE assignment" +
                     "; fixed_premises=" +
                     std::to_string(premises.fixed.size()) +
                     "; equality_premises=" +
                     std::to_string(premises.equalities.size()));
        conflict_with(premises);
        return true;
    }

    ++m_eqmod_true_lemma_propagations;
    LOG_INFO(engine_log(), "singular",
             reason + "; propagating TRUE lemma" +
                 "; fixed_premises=" +
                 std::to_string(premises.fixed.size()) +
                 "; equality_premises=" +
                 std::to_string(premises.equalities.size()));
    propagate_true_atom(atom, premises);
    return false;
}

template <typename CompiledAtom>
bool EqmodEngine::conflict_on_propagated_family(
    std::vector<CompiledAtom> &atoms, const std::string &kind)
{
    if (!enable_true_lemmas())
        return false;
    for (CompiledAtom &atom : atoms)
    {
        if (atom.propagated_truth != Z3_L_TRUE ||
            lbool_of(atom.atom) != Z3_L_FALSE)
            continue;
        ProofPremises premises{atom.propagated_truth_ants,
                               atom.propagated_truth_eqs};
        premises.fixed.push_back(atom.atom);
        const std::string detail =
            kind == "eqmodP1" || kind == "eqmodP2"
                ? " was already implied TRUE; conflicting with FALSE "
                  "assignment without mixed GB"
                : std::string();
        LOG_INFO(engine_log(), "singular",
                 "[" + kind + "] propagated TRUE refute: " +
                     label_of(atom.atom) + detail);
        ++m_eqmod_propagated_assignment_conflicts;
        conflict_with(premises);
        return true;
    }
    return false;
}

bool EqmodEngine::conflict_on_propagated_eqmod_truth()
{
    return conflict_on_propagated_p1_truth() ||
           conflict_on_propagated_p2_truth() ||
           conflict_on_propagated_n_truth();
}

bool EqmodEngine::conflict_on_propagated_p1_truth()
{
    return conflict_on_propagated_family(m_eqmodp, "eqmodP1");
}

bool EqmodEngine::conflict_on_propagated_p2_truth()
{
    return conflict_on_propagated_family(m_eqmodp2, "eqmodP2");
}

bool EqmodEngine::conflict_on_propagated_n_truth()
{
    return conflict_on_propagated_family(m_eqmodp3, "eqmodP3") ||
           conflict_on_propagated_family(m_eqmodp4, "eqmodP4");
}

template <typename CompiledAtom, typename SameModuli, typename AppendModulusGens, typename ConflictCheck>
void EqmodEngine::propagate_true_lemmas_from_context_impl(std::vector<CompiledAtom> &atoms,
                                             const std::string &kind,
                                             const std::string &gb_label,
                                             unsigned family,
                                             const std::string &source_signature,
                                             bool cache_enabled,
                                             SameModuli same_moduli,
                                             AppendModulusGens append_modulus_gens,
                                             ConflictCheck conflict_check)
{
    if (atoms.empty())
        return;

    std::unordered_map<Z3_ast, CachedTrueLemmaMembership> uncached_run;
    auto &membership_cache = cache_enabled
                                 ? m_eqmod_true_lemma_membership_cache[
                                       kind + '|' + source_signature]
                                 : uncached_run;

    std::vector<size_t> uncached;
    uncached.reserve(atoms.size());
    for (size_t idx = 0; idx < atoms.size(); ++idx)
    {
        auto &cp = atoms[idx];
        const Z3_lbool current_value = lbool_of(cp.atom);
        if (current_value == Z3_L_TRUE || cp.propagated_truth == Z3_L_TRUE)
            continue;

        auto found = membership_cache.find((Z3_ast)cp.atom);
        if (found == membership_cache.end())
        {
            uncached.push_back(idx);
            if (cache_enabled)
            {
                ++m_eqmod_true_lemma_cache_misses;
                ++m_eqmod_true_lemma_cache_misses_by_family.at(family);
            }
            continue;
        }

        if (cache_enabled)
        {
            ++m_eqmod_true_lemma_cache_hits;
            ++m_eqmod_true_lemma_cache_hits_by_family.at(family);
        }
        const CachedTrueLemmaMembership &cached = found->second;
        if (!cached.member)
            continue;
        cp.propagated_truth = Z3_L_TRUE;
        cp.propagated_truth_ants = cached.premises.fixed;
        cp.propagated_truth_eqs = cached.premises.equalities;
        if (propagate_true_lemma_or_conflict(
                cp.atom, current_value, cached.premises,
                "[" + kind + "] cached eqmod true/context lemma: " +
                    label_of(cp.atom) + " is implied TRUE"))
            return;
    }

    if (conflict_check() || uncached.empty())
        return;

    ring R = engine_ring();
    rChangeCurrRing(R);

    std::vector<SourceGenerator> base_gens;
    collect_true_context_source_generators(base_gens);

    struct BvFixedGroup
    {
        size_t rep = 0;
        std::vector<size_t> members;
    };

    std::vector<BvFixedGroup> groups;
    for (size_t idx : uncached)
    {
        auto &cp = atoms[idx];

        bool placed = false;
        for (auto &group : groups)
        {
            auto &rep = atoms[group.rep];
            if (same_moduli(cp, rep))
            {
                group.members.push_back(idx);
                placed = true;
                break;
            }
        }
        if (!placed)
            groups.push_back({idx, {idx}});
    }

    const bool use_group_batch =
        !enable_true_lemma_lift_antecedents() &&
        (true_lemma_processes() != 0 ||
         reuse_base_basis());
    if (use_group_batch)
    {
        const std::size_t no_batch = static_cast<std::size_t>(-1);
        std::vector<std::size_t> batch_index(groups.size(), no_batch);
        std::vector<std::vector<SourceGenerator>> modulus_storage(groups.size());
        std::vector<util::singular::MembershipGroup> batch_groups;
        std::vector<poly> base_polys;
        base_polys.reserve(base_gens.size());
        for (const SourceGenerator &generator : base_gens)
            if (generator.gen)
                base_polys.push_back(generator.gen);

        for (std::size_t group_index = 0; group_index < groups.size(); ++group_index)
        {
            BvFixedGroup &group = groups[group_index];
            bool needs_gb = false;
            for (size_t idx : group.members)
                if (atoms[idx].D != nullptr && !base_gens.empty())
                {
                    needs_gb = true;
                    break;
                }

            append_modulus_gens(atoms[group.rep], modulus_storage[group_index]);
            if (!needs_gb)
            {
                // Modulus generators can make an otherwise empty base
                // non-empty, matching the original combined gens test.
                for (const SourceGenerator &generator : modulus_storage[group_index])
                    if (generator.gen)
                    {
                        for (size_t idx : group.members)
                            if (atoms[idx].D != nullptr)
                            {
                                needs_gb = true;
                                break;
                            }
                        if (needs_gb)
                            break;
                    }
            }
            if (!needs_gb)
                continue;

            util::singular::MembershipGroup task;
            task.label = gb_label;
            for (const SourceGenerator &generator : modulus_storage[group_index])
                if (generator.gen)
                    task.extra_generators.push_back(generator.gen);
            for (size_t idx : group.members)
                task.targets.push_back(atoms[idx].D);
            batch_index[group_index] = batch_groups.size();
            batch_groups.push_back(std::move(task));

            const std::size_t equality_generator_count =
                std::count_if(base_gens.begin(), base_gens.end(),
                              [](const SourceGenerator &g)
                              { return g.source_eq.has_value(); });
            trace_true_lemma_gb(
                    true, gb_label, equality_generator_count,
                    base_gens.size() + modulus_storage[group_index].size());
        }

        util::singular::MembershipGroupBatchResult batch;
        try
        {
            batch = run_membership_groups(
                base_polys, batch_groups,
                true_lemma_processes(), false);
            accumulate_membership_group_timing(batch);
        }
        catch (...)
        {
            try
            {
                throw;
            }
            catch (const std::exception &error)
            {
                LOG_INFO(engine_log(), "singular",
                         "TRUE-lemma GB group batch failed: " +
                             std::string(error.what()));
            }
            catch (...)
            {
                LOG_INFO(engine_log(), "singular",
                         "TRUE-lemma GB group batch failed: unknown exception");
            }
            for (auto &storage : modulus_storage)
                delete_source_generators(storage);
            delete_source_generators(base_gens);
            throw;
        }

        bool stop = false;
        for (std::size_t group_index = 0;
             group_index < groups.size() && !stop; ++group_index)
        {
            BvFixedGroup &group = groups[group_index];
            std::vector<SourceGenerator> proof_gens;
            append_modulus_gens(atoms[group.rep], proof_gens);
            for (const SourceGenerator &generator : base_gens)
                if (generator.gen)
                    add_source_generator(
                        proof_gens, p_Copy(generator.gen, R),
                        generator.source_atom, generator.source_eq);

            const bool used_batch = batch_index[group_index] != no_batch;
            const std::vector<bool> *membership = nullptr;
            if (used_batch)
            {
                if (batch_index[group_index] >= batch.groups.size())
                    throw std::runtime_error("missing TRUE-lemma GB group result");
                membership = &batch.groups[batch_index[group_index]].membership;
                if (membership->size() != group.members.size())
                    throw std::runtime_error("TRUE-lemma GB result size mismatch");
            }

            for (std::size_t member_pos = 0;
                 member_pos < group.members.size(); ++member_pos)
            {
                auto &cp = atoms[group.members[member_pos]];
                const bool in = cp.D == nullptr
                                    ? true
                                    : membership != nullptr &&
                                          (*membership)[member_pos];
                ProofPremises proof_premises;
                if (in && cp.D != nullptr)
                    proof_premises = premises_from_source_generators(proof_gens);
                record_membership(family, in);
                membership_cache.insert_or_assign(
                    (Z3_ast)cp.atom,
                    CachedTrueLemmaMembership{in, proof_premises});
                if (!in)
                    continue;
                cp.propagated_truth = Z3_L_TRUE;
                cp.propagated_truth_ants = proof_premises.fixed;
                cp.propagated_truth_eqs = proof_premises.equalities;
                if (propagate_true_lemma_or_conflict(
                        cp.atom, lbool_of(cp.atom), proof_premises,
                        "[" + kind +
                            "] eqmod true/context lemma: " +
                            label_of(cp.atom) + " is implied TRUE"))
                {
                    stop = true;
                    break;
                }
            }

            if (used_batch)
            {
                const std::size_t equality_generator_count =
                    std::count_if(proof_gens.begin(), proof_gens.end(),
                                  [](const SourceGenerator &g)
                                  { return g.source_eq.has_value(); });
                trace_true_lemma_gb(false, gb_label, equality_generator_count,
                                        proof_gens.size());
            }
            delete_source_generators(proof_gens);
            if (conflict_check())
                stop = true;
        }

        for (auto &storage : modulus_storage)
            delete_source_generators(storage);
        delete_source_generators(base_gens);
        return;
    }

    for (auto &group : groups)
    {
        auto &rep = atoms[group.rep];
        std::vector<SourceGenerator> gens;
        gens.reserve(base_gens.size() + 2);
        append_modulus_gens(rep, gens);
        for (const auto &g : base_gens)
            if (g.gen)
                add_source_generator(gens, p_Copy(g.gen, R), g.source_atom, g.source_eq);

        const std::size_t equality_generator_count =
            std::count_if(gens.begin(), gens.end(),
                          [](const SourceGenerator &g) { return g.source_eq.has_value(); });
        const std::size_t total_generator_count = gens.size();

        bool needs_gb = false;
        for (size_t idx : group.members)
        {
            auto &cp = atoms[idx];
            if (cp.D != nullptr && !gens.empty())
            {
                needs_gb = true;
                break;
            }
        }

        std::vector<bool> batch_membership;
        bool used_batch_membership = false;
        util::singular::LiftBatchResult lift_result;
        bool used_lift_prover = false;
        if (needs_gb)
        {
            trace_true_lemma_gb(true, gb_label, equality_generator_count,
                                    total_generator_count);
            if (!enable_true_lemma_lift_antecedents())
            {
                std::vector<poly> generator_polys;
                generator_polys.reserve(gens.size());
                for (const SourceGenerator &generator : gens)
                    generator_polys.push_back(generator.gen);

                std::vector<poly> targets;
                targets.reserve(group.members.size());
                for (size_t idx : group.members)
                    targets.push_back(atoms[idx].D);

                util::singular::MembershipOptions options;
                options.preprocess = preprocess_membership();
                options.verify_preprocess = verify_membership_preprocess();
                options.ideal_rewrite =
                    enable_ideal_rewrite();
                util::singular::MembershipBatchResult result =
                    util::singular::prove_membership(
                        generator_polys, targets, R, options, gb_label, &engine_log());
                accumulate_direct_membership_timing(result.groebner);
                batch_membership = std::move(result.membership);
                used_batch_membership = true;
            }
            else
            {
                std::vector<poly> generator_polys;
                generator_polys.reserve(gens.size());
                for (const SourceGenerator &generator : gens)
                    generator_polys.push_back(generator.gen);

                std::vector<poly> targets;
                std::vector<std::string> target_labels;
                targets.reserve(group.members.size());
                target_labels.reserve(group.members.size());
                for (size_t idx : group.members)
                {
                    targets.push_back(atoms[idx].D);
                    target_labels.push_back("[" + kind + "] " + label_of(atoms[idx].atom));
                }

                util::singular::LiftProverOptions options;
                options.preprocess = preprocess_membership();
                options.verify_preprocess = verify_membership_preprocess();
                options.ideal_rewrite =
                    enable_ideal_rewrite();
                // Preserve the existing behavior: direct lift antecedent
                // extraction is attempted only on preprocessed inputs.
                options.extract_support = preprocess_membership();
                lift_result = util::singular::prove_with_lift_support(
                    generator_polys, targets, target_labels, R,
                    options, gb_label, &engine_log());
                accumulate_direct_membership_timing(lift_result.groebner);
                used_lift_prover = true;
            }
        }
        else
        {
            delete_source_generators(gens);
        }

        bool hit_conflict = false;
        for (size_t member_pos = 0; member_pos < group.members.size(); ++member_pos)
        {
            size_t idx = group.members[member_pos];
            auto &cp = atoms[idx];
            bool in = false;
            if (cp.D == nullptr)
            {
                in = true;
            }
            else if (used_batch_membership && member_pos < batch_membership.size())
            {
                in = batch_membership[member_pos];
            }
            else if (used_lift_prover && member_pos < lift_result.targets.size())
            {
                in = lift_result.targets[member_pos].member;
            }

            ProofPremises proof_premises;
            if (in)
            {
                if (cp.D == nullptr)
                {
                    proof_premises.fixed.clear();
                    proof_premises.equalities.clear();
                }
                else if (!enable_true_lemma_lift_antecedents())
                {
                    proof_premises = premises_from_source_generators(gens);
                }
                else
                {
                    const std::string proof_label = "[" + kind + "] " + label_of(cp.atom);
                    const util::singular::TargetLiftResult *target_result =
                        member_pos < lift_result.targets.size()
                            ? &lift_result.targets[member_pos]
                            : nullptr;
                    if (!preprocess_membership())
                    {
                        LOG_INFO(engine_log(), "singular",
                                 proof_label +
                                     ": direct lift antecedents require --enable-gb-preprocess");
                    }
                    const bool lift_ok = target_result != nullptr &&
                                         target_result->support_certified;
                    if (lift_ok)
                    {
                        proof_premises = premises_from_source_generators(
                            gens, &target_result->used_generator_indices);
                        const ProofPremises all_premises =
                            premises_from_source_generators(
                                gens, &lift_result.active_generator_indices);
                        const std::size_t used_count =
                            proof_premises.fixed.size() + proof_premises.equalities.size();
                        const std::size_t all_count =
                            all_premises.fixed.size() + all_premises.equalities.size();
                        LOG_INFO(engine_log(), "singular",
                                 proof_label + ": direct lift TRUE lemma antecedents " +
                                     std::to_string(used_count) + " / " +
                                     std::to_string(all_count));

                        std::unordered_set<std::size_t> used_indices(
                            target_result->used_generator_indices.begin(),
                            target_result->used_generator_indices.end());
                        std::unordered_set<Z3_ast> omitted_seen;
                        for (std::size_t source_idx : lift_result.active_generator_indices)
                        {
                            if (source_idx >= gens.size() ||
                                used_indices.count(source_idx) != 0 ||
                                (!gens[source_idx].source_atom.has_value() &&
                                 !gens[source_idx].source_eq.has_value()))
                                continue;
                            if (gens[source_idx].source_atom.has_value())
                            {
                                const expr &source = *gens[source_idx].source_atom;
                                if (omitted_seen.insert((Z3_ast)source).second)
                                    LOG_INFO(engine_log(), "singular",
                                             proof_label +
                                                 ": direct lift omitted antecedent " +
                                                 label_of(source));
                            }
                            else
                            {
                                const auto &[lhs, rhs] = *gens[source_idx].source_eq;
                                LOG_INFO(engine_log(), "singular",
                                         proof_label +
                                             ": direct lift omitted equality " +
                                             lhs.to_string() + " == " + rhs.to_string());
                            }
                        }
                    }
                    if (!lift_ok)
                    {
                        LOG_INFO(engine_log(), "singular",
                                     proof_label +
                                         ": direct lift certificate unavailable for ideal of size " +
                                     std::to_string(lift_result.preprocessed_generator_count) +
                                         "; using full antecedents");
                        proof_premises = premises_from_source_generators(
                            gens, &lift_result.active_generator_indices);
                    }
                }

            }

            record_membership(family, in);
            membership_cache.insert_or_assign(
                (Z3_ast)cp.atom,
                CachedTrueLemmaMembership{in, proof_premises});

            if (in)
            {
                cp.propagated_truth = Z3_L_TRUE;
                cp.propagated_truth_ants = proof_premises.fixed;
                cp.propagated_truth_eqs = proof_premises.equalities;
                if (propagate_true_lemma_or_conflict(
                        cp.atom,
                        lbool_of(cp.atom),
                        proof_premises,
                        "[" + kind + "] eqmod true/context lemma: " + label_of(cp.atom) + " is implied TRUE"))
                {
                    hit_conflict = true;
                    break;
                }
            }
        }

        delete_source_generators(gens);

        if (needs_gb)
            trace_true_lemma_gb(false, gb_label, equality_generator_count,
                                    total_generator_count);

        if (hit_conflict || conflict_check())
        {
            delete_source_generators(base_gens);
            return;
        }
    }

    delete_source_generators(base_gens);
}

void EqmodEngine::propagate_eqmodP1_true_lemmas_from_context_impl(
    const std::string &source_signature, bool cache_enabled)
{
    ring R = engine_ring();
    propagate_true_lemmas_from_context_impl(
        m_eqmodp,
        "eqmodP1",
        "eqmodP1-true-lemma",
        1,
        source_signature,
        cache_enabled,
        [R](const P1Compiled &a, const P1Compiled &b)
        {
            return same_poly(a.M_poly, b.M_poly, R);
        },
        [this, R](const P1Compiled &cp, std::vector<SourceGenerator> &gens)
        {
            if (cp.M_poly)
                add_source_generator(gens, p_Copy(cp.M_poly, R), std::nullopt);
        },
        [this]()
        {
            return conflict_on_propagated_family(m_eqmodp, "eqmodP1");
        });
}

void EqmodEngine::propagate_eqmodP2_true_lemmas_from_context_impl(
    const std::string &source_signature, bool cache_enabled)
{
    ring R = engine_ring();
    propagate_true_lemmas_from_context_impl(
        m_eqmodp2,
        "eqmodP2",
        "eqmodP2-true-lemma",
        2,
        source_signature,
        cache_enabled,
        [R](const P2Compiled &a, const P2Compiled &b)
        {
            return same_poly(a.M1_poly, b.M1_poly, R) &&
                   same_poly(a.M2_poly, b.M2_poly, R);
        },
        [this, R](const P2Compiled &cp, std::vector<SourceGenerator> &gens)
        {
            if (cp.M1_poly)
                add_source_generator(gens, p_Copy(cp.M1_poly, R), std::nullopt);
            if (cp.M2_poly)
                add_source_generator(gens, p_Copy(cp.M2_poly, R), std::nullopt);
        },
        [this]()
        {
            return conflict_on_propagated_family(m_eqmodp2, "eqmodP2");
        });
}

void EqmodEngine::propagate_eqmodN_true_lemmas_from_context_impl(
    std::vector<NCompiled> &atoms,
    const std::string &kind,
    const std::string &source_signature,
    bool cache_enabled)
{
    ring R = engine_ring();
    propagate_true_lemmas_from_context_impl(
        atoms, kind, kind + "-true-lemma", atoms.empty() ? 0 : atoms[0].arity,
        source_signature, cache_enabled,
        [R](const NCompiled &a, const NCompiled &b)
        {
            if (a.modulus_polys.size() != b.modulus_polys.size())
                return false;
            for (std::size_t i = 0; i < a.modulus_polys.size(); ++i)
                if (!same_poly(a.modulus_polys[i], b.modulus_polys[i], R))
                    return false;
            return true;
        },
        [this, R](const NCompiled &cp,
                  std::vector<SourceGenerator> &gens)
        {
            for (poly modulus : cp.modulus_polys)
                if (modulus)
                    add_source_generator(gens, p_Copy(modulus, R), std::nullopt);
        },
        [this, &atoms, kind]()
        {
            return conflict_on_propagated_family(atoms, kind);
        });
}

void EqmodEngine::propagate_eqmod_true_lemmas_from_context(bool force)
{
    if (!enable_true_lemmas())
        return;
    if (m_eqmodp.empty() && m_eqmodp2.empty() &&
        m_eqmodp3.empty() && m_eqmodp4.empty())
        return;

    ring R = engine_ring();
    if (R == nullptr)
        return;
    rChangeCurrRing(R);

    if (!all_eqp_fixed())
        return;

    std::size_t p1_count = m_eqmodp.size();
    std::size_t p2_count = m_eqmodp2.size();
    std::size_t p3_count = m_eqmodp3.size();
    std::size_t p4_count = m_eqmodp4.size();
    std::string source_signature;
    const bool cache_enabled = enable_true_lemma_cache();
    if (!cache_enabled)
    {
        const std::size_t true_count = true_context_atom_count();
        if (true_count == m_last_eqmod_true_lemma_true_count &&
            p1_count == m_last_eqmod_true_lemma_p1_count &&
            p2_count == m_last_eqmod_true_lemma_p2_count &&
            p3_count == m_last_eqmod_true_lemma_p3_count &&
            p4_count == m_last_eqmod_true_lemma_p4_count &&
            equality_generator_epoch() ==
                m_last_eqmod_true_lemma_eq_generator_epoch)
            return;
        m_last_eqmod_true_lemma_true_count = true_count;
        m_last_eqmod_true_lemma_p1_count = p1_count;
        m_last_eqmod_true_lemma_p2_count = p2_count;
        m_last_eqmod_true_lemma_p3_count = p3_count;
        m_last_eqmod_true_lemma_p4_count = p4_count;
        m_last_eqmod_true_lemma_eq_generator_epoch =
            equality_generator_epoch();
    }
    else
    {
        source_signature = true_context_source_signature();
        const std::size_t target_count = p1_count + p2_count + p3_count + p4_count;
        const std::size_t source_batch_size =
            target_count <= 8
                ? 1
                : std::min<std::size_t>(
                      64, std::max<std::size_t>(1, target_count / 2));
        const bool source_changed =
            source_signature !=
            m_last_eqmod_true_lemma_source_signature;
        if (source_changed && !force &&
            !m_eqmod_true_lemma_replay_needed)
        {
            if (source_signature !=
                m_pending_eqmod_true_lemma_source_signature)
            {
                m_pending_eqmod_true_lemma_source_signature =
                    source_signature;
                ++m_pending_eqmod_true_lemma_source_updates;
            }
            if (m_pending_eqmod_true_lemma_source_updates <
                source_batch_size)
            {
                ++m_deferred_eqmod_true_lemma_checks;
                return;
            }
        }
        if (!m_eqmod_true_lemma_replay_needed &&
            source_signature ==
                m_last_eqmod_true_lemma_source_signature &&
            p1_count == m_last_eqmod_true_lemma_p1_count &&
            p2_count == m_last_eqmod_true_lemma_p2_count &&
            p3_count == m_last_eqmod_true_lemma_p3_count &&
            p4_count == m_last_eqmod_true_lemma_p4_count)
            return;
        m_last_eqmod_true_lemma_source_signature = source_signature;
        m_last_eqmod_true_lemma_p1_count = p1_count;
        m_last_eqmod_true_lemma_p2_count = p2_count;
        m_last_eqmod_true_lemma_p3_count = p3_count;
        m_last_eqmod_true_lemma_p4_count = p4_count;
        m_eqmod_true_lemma_replay_needed = false;
        m_pending_eqmod_true_lemma_source_signature = source_signature;
        m_pending_eqmod_true_lemma_source_updates = 0;
    }

    if (!m_eqmodp.empty())
        propagate_eqmodP1_true_lemmas_from_context_impl(
            source_signature, cache_enabled);
    if (conflict_on_propagated_family(m_eqmodp, "eqmodP1"))
        return;
    if (!m_eqmodp2.empty())
        propagate_eqmodP2_true_lemmas_from_context_impl(
            source_signature, cache_enabled);
    if (conflict_on_propagated_family(m_eqmodp2, "eqmodP2"))
        return;
    if (!m_eqmodp3.empty())
        propagate_eqmodN_true_lemmas_from_context_impl(
            m_eqmodp3, "eqmodP3", source_signature, cache_enabled);
    if (conflict_on_propagated_family(m_eqmodp3, "eqmodP3"))
        return;
    if (!m_eqmodp4.empty())
        propagate_eqmodN_true_lemmas_from_context_impl(
            m_eqmodp4, "eqmodP4", source_signature, cache_enabled);
}

} // namespace eqmod
