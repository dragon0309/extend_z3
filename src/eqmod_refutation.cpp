#include "eqmod_engine.hpp"

#include <algorithm>
#include <sstream>
#include <stdexcept>

#include "util/singular_poly.hpp"

using namespace z3;
using util::singular::copy_poly_or_null;
using util::singular::delete_poly_if_nonnull;
using util::singular::poly_from_si;
using util::singular::poly_mul_clone;
using util::singular::ScopedPolyOwner;

namespace eqmod
{
EqmodEngine::SourceGenerator::SourceGenerator(
    poly generator,
    std::optional<expr> atom,
    std::optional<std::pair<expr, expr>> equality,
    ring current_ring)
    : gen(generator), source_atom(std::move(atom)),
      source_eq(std::move(equality)), owner_ring(current_ring)
{
}

EqmodEngine::SourceGenerator::~SourceGenerator()
{
    if (gen && owner_ring)
    {
        rChangeCurrRing(owner_ring);
        delete_poly_if_nonnull(gen, owner_ring);
    }
}

EqmodEngine::SourceGenerator::SourceGenerator(SourceGenerator &&other) noexcept
    : gen(std::exchange(other.gen, nullptr)),
      source_atom(std::move(other.source_atom)),
      source_eq(std::move(other.source_eq)),
      owner_ring(std::exchange(other.owner_ring, nullptr))
{
}

EqmodEngine::SourceGenerator &
EqmodEngine::SourceGenerator::operator=(SourceGenerator &&other) noexcept
{
    if (this == &other)
        return *this;
    if (gen && owner_ring)
    {
        rChangeCurrRing(owner_ring);
        delete_poly_if_nonnull(gen, owner_ring);
    }
    gen = std::exchange(other.gen, nullptr);
    source_atom = std::move(other.source_atom);
    source_eq = std::move(other.source_eq);
    owner_ring = std::exchange(other.owner_ring, nullptr);
    return *this;
}
void EqmodEngine::delete_source_generators(
    std::vector<SourceGenerator> &sources) const
{
    sources.clear();
}

void EqmodEngine::add_source_generator(
    std::vector<SourceGenerator> &sources,
    poly generator,
    std::optional<expr> source_atom,
    std::optional<std::pair<expr, expr>> source_equality) const
{
    if (generator == nullptr)
        return;
    sources.emplace_back(generator, std::move(source_atom),
                         std::move(source_equality), engine_ring());
}

EqmodEngine::ProofPremises EqmodEngine::premises_from_source_generators(
    const std::vector<SourceGenerator> &sources,
    const std::vector<std::size_t> *used_indices) const
{
    ProofPremises premises;
    std::unordered_set<Z3_ast> seen_fixed;
    std::unordered_set<std::string> seen_equalities;

    auto add_source = [&](std::size_t index)
    {
        if (index >= sources.size())
            return;
        const SourceGenerator &source = sources[index];
        if (source.source_atom)
        {
            const expr &atom = *source.source_atom;
            if (seen_fixed.insert((Z3_ast)atom).second)
                premises.fixed.push_back(atom);
        }
        if (source.source_eq)
        {
            const auto &[lhs, rhs] = *source.source_eq;
            const unsigned lhs_id = Z3_get_ast_id(
                (Z3_context)lhs.ctx(), (Z3_ast)lhs);
            const unsigned rhs_id = Z3_get_ast_id(
                (Z3_context)rhs.ctx(), (Z3_ast)rhs);
            const std::string key =
                std::to_string(std::min(lhs_id, rhs_id)) + ':' +
                std::to_string(std::max(lhs_id, rhs_id));
            if (seen_equalities.insert(key).second)
                premises.equalities.emplace_back(lhs, rhs);
        }
    };

    if (used_indices)
        for (std::size_t index : *used_indices)
            add_source(index);
    else
        for (std::size_t index = 0; index < sources.size(); ++index)
            add_source(index);
    return premises;
}

bool EqmodEngine::prove_eqmod_membership(const std::vector<SourceGenerator> &sources,
                                const std::vector<poly> &extra_generators,
                                poly target,
                                const std::string &label,
                                unsigned family)
    {
        if (target == nullptr)
        {
            record_membership(family, true);
            return true;
        }
        std::vector<poly> generators;
        generators.reserve(sources.size() + extra_generators.size());
        for (const SourceGenerator &source : sources)
            if (source.gen)
                generators.push_back(source.gen);
        for (poly generator : extra_generators)
            if (generator)
                generators.push_back(generator);
        if (generators.empty())
        {
            record_membership(family, false);
            return false;
        }

        if (label.find("final-validation") == std::string::npos &&
            (refutation_processes() != 0 || reuse_base_basis()))
        {
            std::vector<poly> base;
            for (const SourceGenerator &source : sources)
                if (source.gen)
                    base.push_back(source.gen);
            util::singular::MembershipGroup group;
            group.label = label;
            for (poly generator : extra_generators)
                if (generator)
                    group.extra_generators.push_back(generator);
            group.targets.push_back(target);
            util::singular::MembershipGroupBatchResult batch =
                run_membership_groups(base, {group}, refutation_processes(),
                                      false);
            accumulate_membership_group_timing(batch);
            const bool member = !batch.groups.empty() &&
                                !batch.groups[0].membership.empty() &&
                                batch.groups[0].membership[0];
            record_membership(family, member);
            return member;
        }

        util::singular::MembershipOptions options;
        options.preprocess = preprocess_membership();
        options.verify_preprocess = verify_membership_preprocess();
        options.ideal_rewrite = enable_ideal_rewrite();
        util::singular::MembershipBatchResult result =
            util::singular::prove_membership(
                generators, {target}, engine_ring(), options, label, &engine_log());
        accumulate_direct_membership_timing(result.groebner);
        const bool member = !result.membership.empty() && result.membership[0];
        record_membership(family, member);
        return member;
    }

void EqmodEngine::check_cross_family_eqmod_refutations(bool force)
    {
        struct Target
        {
            expr atom;
            poly difference;
            std::vector<poly> moduli;
            unsigned family;
        };
        std::vector<Target> targets;
        targets.reserve(m_eqmodp.size() + m_eqmodp2.size() +
                        m_eqmodp3.size() + m_eqmodp4.size());
        for (const auto &cp : m_eqmodp)
            targets.push_back({cp.atom, cp.D, {cp.M_poly}, 1});
        for (const auto *family : {&m_eqmodp2, &m_eqmodp3, &m_eqmodp4})
            for (const auto &cp : *family)
                targets.push_back({cp.atom, cp.D, cp.modulus_polys, cp.arity});
        if (targets.empty())
            return;

        bool any_true = false;
        bool any_false = false;
        bool any_undefined = false;
        for (const Target &target : targets)
        {
            const Z3_lbool value = lbool_of(target.atom);
            any_true = any_true || value == Z3_L_TRUE;
            any_false = any_false || value == Z3_L_FALSE;
            any_undefined = any_undefined || value == Z3_L_UNDEF;
        }

        const std::string source_signature = true_context_source_signature();
        std::vector<SourceGenerator> sources;
        collect_true_context_source_generators(sources);

        const bool source_batch_due =
            force || sources.size() <= 8;

        std::ostringstream false_signature_builder;
        for (const Target &target : targets)
            if (lbool_of(target.atom) == Z3_L_FALSE)
                false_signature_builder << (Z3_ast)target.atom << ';';
        const std::string false_signature = false_signature_builder.str();
        const bool false_targets_changed =
            false_signature != m_last_eqmod_refutation_false_signature;

        // A unit TRUE context is inconsistent immediately.  Do not wait for
        // unrelated modular atoms to become fixed, and do not require every
        // currently fixed modular atom to be TRUE.
        if (enable_all_true() && source_batch_due && !sources.empty() &&
            m_eqmod_unit_nonmember_cache.count(source_signature) == 0)
        {
            poly one = poly_from_si(1, engine_ring());
            const bool inconsistent = prove_eqmod_membership(
                sources, {}, one, "eqmod-all-true", 0);
            delete_poly_if_nonnull(one, engine_ring());
            if (inconsistent)
            {
                ProofPremises premises = premises_from_source_generators(sources);
                LOG_INFO(engine_log(), "singular",
                         "[eqmodP1-P4] all-true refute: 1 is in the complete TRUE witness ideal");
                ++m_eqmod_unit_conflicts;
                conflict_with(premises);
                delete_source_generators(sources);
                return;
            }
            m_eqmod_unit_nonmember_cache.insert(source_signature);
        }

        const bool permit_false_target_check =
            any_false && ((any_true && enable_mixed()) ||
                          (!any_true && enable_all_false()));
        // Pure all-false checks are most useful as a tuple-grouped batch.  A
        // fixed callback arrives once per atom, so querying while sibling
        // atoms are still undefined would permanently split the batch via the
        // non-member cache.  Mixed checks remain immediate because their TRUE
        // source context can already prove a useful conflict.
        if (!force && !any_true && any_false && any_undefined &&
            targets.size() > 1)
        {
            ++m_deferred_eqmod_refutation_checks;
            delete_source_generators(sources);
            return;
        }
        if (!permit_false_target_check ||
            (!source_batch_due && !false_targets_changed))
        {
            if (!source_batch_due && (any_true || any_false))
                ++m_deferred_eqmod_refutation_checks;
            delete_source_generators(sources);
            return;
        }
        m_last_eqmod_refutation_false_signature = false_signature;
        auto &known_nonmembers =
            m_eqmod_refutation_nonmember_cache[source_signature];
        for (const Target &target : targets)
            if (lbool_of(target.atom) == Z3_L_FALSE && target.difference == nullptr)
            {
                ProofPremises premises = premises_from_source_generators(sources);
                premises.fixed.push_back(target.atom);
                record_membership(target.family, true);
                if (any_true)
                    ++m_eqmod_mixed_conflicts;
                else
                    ++m_eqmod_all_false_conflicts;
                ++m_eqmod_refutation_conflicts_by_family.at(target.family);
                conflict_with(premises);
                delete_source_generators(sources);
                return;
            }

        // --m-prime is an explicit user promise that each shared P1 modulus
        // handled here generates a prime ideal.  If
        //
        //   product(D_i) = Q*M + sum(H_j*E_j),
        //
        // the TRUE source premises make every E_j zero, and primality of
        // <M> implies that at least one D_i belongs to <M>.  This contradicts
        // the complete all-FALSE assignment for the group.  A failed product
        // query proves nothing about an individual factor, so the normal
        // per-target batch below remains the mandatory fallback.
        if (!any_true && enable_all_false() && assume_p1_modulus_prime())
        {
            struct PrimeProductGroup
            {
                std::size_t representative = 0;
                std::vector<std::size_t> members;
            };
            std::vector<PrimeProductGroup> product_groups;
            for (std::size_t index = 0; index < targets.size(); ++index)
            {
                const Target &target = targets[index];
                if (target.family != 1 ||
                    lbool_of(target.atom) != Z3_L_FALSE ||
                    target.difference == nullptr || target.moduli.size() != 1 ||
                    target.moduli[0] == nullptr)
                    continue;

                bool placed = false;
                for (PrimeProductGroup &group : product_groups)
                {
                    const Target &representative = targets[group.representative];
                    if (!same_poly(representative.moduli[0],
                                            target.moduli[0], engine_ring()))
                        continue;
                    group.members.push_back(index);
                    placed = true;
                    break;
                }
                if (!placed)
                    product_groups.push_back({index, {index}});
            }

            for (const PrimeProductGroup &group : product_groups)
            {
                if (group.members.size() < 2)
                    continue;

                std::ostringstream cache_key_builder;
                cache_key_builder << source_signature << "|P1-prime-product|";
                for (std::size_t member : group.members)
                    cache_key_builder << (Z3_ast)targets[member].atom << ';';
                const std::string cache_key = cache_key_builder.str();
                auto conflict_from_product = [&](bool cached)
                {
                    ++m_eqmod_p1_product_conflicts;
                    ++m_eqmod_all_false_conflicts;
                    ++m_eqmod_refutation_conflicts_by_family.at(1);
                    ProofPremises premises =
                        premises_from_source_generators(sources);
                    for (std::size_t member_index : group.members)
                        premises.fixed.push_back(targets[member_index].atom);
                    LOG_INFO(engine_log(), "singular",
                             "[eqmodP1] all-false prime-product refute" +
                                 std::string(cached ? " (cached)" : "") +
                                 ": product of " +
                                 std::to_string(group.members.size()) +
                                 " FALSE differences is in <shared promised-prime "
                                 "modulus, complete TRUE context>");
                    conflict_with(premises);
                };
                if (m_eqmod_p1_product_member_cache.count(cache_key) != 0)
                {
                    ++m_eqmod_p1_product_cache_hits;
                    conflict_from_product(true);
                    delete_source_generators(sources);
                    return;
                }
                if (m_eqmod_p1_product_nonmember_cache.count(cache_key) != 0)
                {
                    ++m_eqmod_p1_product_cache_hits;
                    continue;
                }

                ScopedPolyOwner product(
                    engine_ring(), copy_poly_or_null(
                                targets[group.members[0]].difference, engine_ring()));
                for (std::size_t position = 1;
                     position < group.members.size(); ++position)
                {
                    product.reset(poly_mul_clone(
                        product.get(), targets[group.members[position]].difference,
                        engine_ring()));
                }

                ++m_eqmod_p1_product_queries;
                const Target &representative = targets[group.representative];
                const bool member = prove_eqmod_membership(
                    sources, {representative.moduli[0]}, product.get(),
                    "eqmodP1-all-false-prime-product", 1);
                if (!member)
                {
                    ++m_eqmod_p1_product_nonmembers;
                    m_eqmod_p1_product_nonmember_cache.insert(cache_key);
                    continue;
                }

                ++m_eqmod_p1_product_members;
                m_eqmod_p1_product_member_cache.insert(cache_key);
                conflict_from_product(false);
                delete_source_generators(sources);
                return;
            }
        }

        struct FalseGroup
        {
            std::size_t representative = 0;
            std::vector<std::size_t> members;
            std::size_t batch_index = static_cast<std::size_t>(-1);
        };
        std::vector<FalseGroup> groups;
        for (std::size_t index = 0; index < targets.size(); ++index)
        {
            const Target &target = targets[index];
            if (lbool_of(target.atom) != Z3_L_FALSE ||
                target.difference == nullptr)
                continue;
            if (known_nonmembers.count((Z3_ast)target.atom) != 0)
            {
                ++m_eqmod_refutation_cache_hits_by_family.at(target.family);
                continue;
            }
            ++m_eqmod_refutation_cache_misses_by_family.at(target.family);
            bool placed = false;
            for (FalseGroup &group : groups)
            {
                const Target &representative = targets[group.representative];
                if (representative.family != target.family ||
                    representative.moduli.size() != target.moduli.size())
                    continue;
                bool same = true;
                for (std::size_t i = 0; i < target.moduli.size(); ++i)
                    same = same && same_poly(
                                       representative.moduli[i], target.moduli[i], engine_ring());
                if (!same)
                    continue;
                group.members.push_back(index);
                placed = true;
                break;
            }
            if (!placed)
                groups.push_back({index, {index}});
        }

        std::vector<poly> base;
        for (const SourceGenerator &source : sources)
            if (source.gen)
                base.push_back(source.gen);
        std::vector<util::singular::MembershipGroup> batch_groups;
        for (FalseGroup &group : groups)
        {
            const Target &representative = targets[group.representative];
            bool have_generator = !base.empty();
            util::singular::MembershipGroup task;
            task.label = "eqmodP" + std::to_string(representative.family) +
                         (any_true ? "-mixed" : "-all-false");
            for (poly modulus : representative.moduli)
                if (modulus)
                {
                    task.extra_generators.push_back(modulus);
                    have_generator = true;
                }
            if (!have_generator)
                continue;
            for (std::size_t member : group.members)
                task.targets.push_back(targets[member].difference);
            group.batch_index = batch_groups.size();
            batch_groups.push_back(std::move(task));
        }

        util::singular::MembershipGroupBatchResult batch;
        if (!batch_groups.empty())
        {
            std::size_t batch_target_count = 0;
            for (const auto &group : batch_groups)
                batch_target_count += group.targets.size();
            LOG_INFO(engine_log(), "singular",
                     "eqmod refutation batch: mode=" +
                         std::string(any_true ? "mixed" : "all-false") +
                         " groups=" + std::to_string(batch_groups.size()) +
                         " targets=" + std::to_string(batch_target_count));
            batch = run_membership_groups(base, batch_groups,
                                          refutation_processes(), false);
            accumulate_membership_group_timing(batch);
        }

        for (const FalseGroup &group : groups)
        {
            const std::vector<bool> *membership = nullptr;
            if (group.batch_index != static_cast<std::size_t>(-1))
                membership = &batch.groups.at(group.batch_index).membership;
            for (std::size_t position = 0; position < group.members.size(); ++position)
            {
                const Target &target = targets[group.members[position]];
                const bool member = target.difference == nullptr ||
                                    (membership && position < membership->size() &&
                                     (*membership)[position]);
                record_membership(target.family, member);
                if (!member)
                {
                    known_nonmembers.insert((Z3_ast)target.atom);
                    continue;
                }

                ProofPremises premises = premises_from_source_generators(sources);
                premises.fixed.push_back(target.atom);
                LOG_INFO(engine_log(), "singular", "[eqmodP1-P4] " +
                             std::string(any_true ? "mixed" : "all-false") +
                             " refute: " + label_of(target.atom) +
                             " difference is in <target moduli, complete TRUE context>");
                if (any_true)
                    ++m_eqmod_mixed_conflicts;
                else
                    ++m_eqmod_all_false_conflicts;
                ++m_eqmod_refutation_conflicts_by_family.at(target.family);
                conflict_with(premises);
                delete_source_generators(sources);
                return;
            }
        }
        delete_source_generators(sources);
    }


} // namespace eqmod

