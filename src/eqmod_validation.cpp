#include "eqmod_engine.hpp"

#include <algorithm>
#include <stdexcept>
#include <unordered_set>

#include "util/singular_poly.hpp"

using namespace z3;
using util::singular::delete_poly_if_nonnull;
using util::singular::delete_polys;
using util::singular::poly_add_owned;
using util::singular::poly_negate_owned;
using util::singular::ScopedPolyOwner;
using util::singular::lowering::CoeffVarMap;
using util::singular::lowering::IndetEnv;
using util::singular::lowering::is_ctor;
using util::singular::lowering::polyterm_to_singular_poly;
using util::singular::lowering::RingEnv;

namespace eqmod
{

int semantic_atom_moduli(const expr &e)
{
    if (!e.is_app() || !e.is_bool())
        return -1;
    const std::string name = e.decl().name().str();
    if (name == "eqP")
        return e.num_args() == 2 ? 0 : -1;
    if (name.size() != 7 || name.compare(0, 6, "eqmodP") != 0)
        return -1;
    const int moduli = name[6] - '0';
    if (moduli < 1 || moduli > 4 ||
        e.num_args() != static_cast<unsigned>(moduli) + 2)
        return -1;
    return moduli;
}

bool EqmodEngine::final_fixed_value_check_all_eqmods()
{
    ring current_ring = engine_ring();
    rChangeCurrRing(current_ring);

    struct ValidationTask
    {
        expr atom;
        expr A;
        expr B;
        std::vector<expr> modulus_terms;
        poly difference = nullptr;
        std::vector<poly> generators;
        std::vector<poly> assignments;
        unsigned family = 0;
        Z3_lbool assigned = Z3_L_UNDEF;
        bool semantic_truth = false;
        // An opaque (Poly Int) symbol left in the membership has no value in
        // the model and stays a free variable, so membership decides truth for
        // every value of it.
        bool opaque = false;
        std::size_t batch_group = static_cast<std::size_t>(-1);
        std::size_t batch_position = static_cast<std::size_t>(-1);
    };

    std::vector<ValidationTask> tasks;
    struct ValidationTasksOwner
    {
        std::vector<ValidationTask> &tasks;
        ring current_ring;
        ~ValidationTasksOwner()
        {
            for (ValidationTask &task : tasks)
                delete_polys(task.assignments, current_ring);
        }
    } tasks_owner{tasks, current_ring};

    auto prepare = [&](const expr &atom,
                       const expr &A,
                       const expr &B,
                       const std::vector<expr> &modulus_terms,
                       poly difference,
                       const std::vector<poly> &modulus_polys,
                       unsigned family)
    {
        const Z3_lbool assigned = lbool_of(atom);
        if (assigned == Z3_L_UNDEF)
            return;

        std::vector<poly> assignments;
        std::string skip_reason;
        if (!build_validation_assignments(
                A, B, modulus_terms, assignments, skip_reason))
        {
            ++m_eqmod_validation_skipped.at(family);
            ++m_eqmod_validation_skip_reasons.at(family)[skip_reason];
            m_semantic_validation_incomplete = true;
            m_final_round_unverified.push_back(
                label_of(atom) + " not checked (" + skip_reason + ")");
            LOG_INFO(engine_log(), "singular",
                     "[eqmodP" + std::to_string(family) +
                         "] final validation incomplete: " + label_of(atom) +
                         " reason=" + skip_reason);
            return;
        }

        std::vector<poly> generators = modulus_polys;
        generators.insert(generators.end(), assignments.begin(),
                          assignments.end());
        // A symbol that cancels in A - B and is absent from the moduli does
        // not take part in the membership, which then decides the atom.
        const bool opaque =
            mentions_opaque_symbol(difference, current_ring) ||
            std::any_of(modulus_polys.begin(), modulus_polys.end(),
                        [&](poly modulus)
                        { return mentions_opaque_symbol(modulus, current_ring); });
        tasks.push_back({atom, A, B, modulus_terms, difference,
                         std::move(generators), std::move(assignments),
                         family, assigned, difference == nullptr, opaque});
    };

    for (const P1Compiled &atom : m_eqmodp)
        prepare(atom.atom, atom.A, atom.B, {atom.Mterm}, atom.D,
                {atom.M_poly}, 1);
    for (const auto *family : {&m_eqmodp2, &m_eqmodp3, &m_eqmodp4})
        for (const NCompiled &atom : *family)
            prepare(atom.atom, atom.A, atom.B, atom.modulus_terms, atom.D,
                    atom.modulus_polys, atom.arity);

    struct ValidationGroup
    {
        std::size_t representative = 0;
        std::vector<std::size_t> members;
        std::size_t batch_index = static_cast<std::size_t>(-1);
    };
    std::vector<ValidationGroup> groups;
    for (std::size_t index = 0; index < tasks.size(); ++index)
    {
        if (tasks[index].difference == nullptr ||
            tasks[index].generators.empty())
            continue;
        bool placed = false;
        for (std::size_t group_index = 0;
             group_index < groups.size(); ++group_index)
        {
            ValidationGroup &group = groups[group_index];
            const auto &lhs = tasks[group.representative].generators;
            const auto &rhs = tasks[index].generators;
            if (lhs.size() != rhs.size())
                continue;
            bool same = true;
            for (std::size_t i = 0; i < lhs.size(); ++i)
                same = same && same_poly(lhs[i], rhs[i], current_ring);
            if (!same)
                continue;
            tasks[index].batch_group = group_index;
            tasks[index].batch_position = group.members.size();
            group.members.push_back(index);
            placed = true;
            break;
        }
        if (!placed)
        {
            tasks[index].batch_group = groups.size();
            tasks[index].batch_position = 0;
            groups.push_back({index, {index}});
        }
    }

    std::vector<util::singular::MembershipGroup> batch_groups;
    batch_groups.reserve(groups.size());
    for (ValidationGroup &group : groups)
    {
        util::singular::MembershipGroup batch_group;
        const ValidationTask &representative =
            tasks[group.representative];
        batch_group.label = "eqmod-final-validation-group";
        batch_group.extra_generators = representative.generators;
        for (std::size_t member : group.members)
            batch_group.targets.push_back(tasks[member].difference);
        group.batch_index = batch_groups.size();
        batch_groups.push_back(std::move(batch_group));
    }

    util::singular::MembershipGroupBatchResult batch;
    if (!batch_groups.empty())
    {
        LOG_INFO(engine_log(), "singular",
                 "eqmod final validation batch: tasks=" +
                     std::to_string(tasks.size()) + " groups=" +
                     std::to_string(batch_groups.size()));
        batch = run_membership_groups({}, batch_groups, 0, false);
        accumulate_membership_group_timing(batch);
        if (batch.groups.size() != batch_groups.size())
            throw std::runtime_error(
                "final validation membership group count mismatch");
    }

    for (const ValidationGroup &group : groups)
    {
        const auto &membership = batch.groups[group.batch_index].membership;
        if (membership.size() != group.members.size())
            throw std::runtime_error(
                "final validation membership result size mismatch");
        for (std::size_t position = 0; position < group.members.size();
             ++position)
            tasks[group.members[position]].semantic_truth =
                membership[position];
    }

    for (ValidationTask &task : tasks)
    {
        record_membership(task.family, task.semantic_truth);
        if (task.opaque && !task.semantic_truth)
        {
            // Membership holding for every value of the opaque symbols also
            // holds for the model's value; failing only shows that some value
            // falsifies the atom, which decides nothing about this model.
            ++m_eqmod_validation_skipped.at(task.family);
            ++m_eqmod_validation_skip_reasons.at(task.family)
                  ["opaque-poly-symbol"];
            m_semantic_validation_incomplete = true;
            m_final_round_unverified.push_back(
                label_of(task.atom) + " not checked (opaque-poly-symbol)");
            LOG_INFO(engine_log(), "singular",
                     "[eqmodP" + std::to_string(task.family) +
                         "] final validation incomplete: " +
                         label_of(task.atom) + " reason=opaque-poly-symbol");
            continue;
        }
        ++m_eqmod_validation_checked.at(task.family);
        const bool assigned_truth = task.assigned == Z3_L_TRUE;
        if (assigned_truth == task.semantic_truth)
        {
            ++m_eqmod_validation_matched.at(task.family);
            continue;
        }

        ++m_eqmod_validation_conflicted.at(task.family);
        LOG_INFO(engine_log(), "singular",
                 "[eqmodP" + std::to_string(task.family) +
                     "] final validation conflict: " + label_of(task.atom) +
                     " assigned=" + (assigned_truth ? "true" : "false") +
                     " semantic=" +
                     (task.semantic_truth ? "true" : "false"));
        conflict_with(validation_conflict_premises(
            task.atom, task.A, task.B, task.modulus_terms));
        return false;
    }
    for (const auto &[atom, description] : m_uninterpreted_eqmod_atoms)
        if (lbool_of(atom) != Z3_L_UNDEF)
            m_final_round_unverified.push_back(description);
    return true;
}

ModelCheckResult EqmodEngine::check_model(
    const z3::model &candidate,
    const expr_vector &assertions,
    const IndetEnv &indets,
    const std::vector<std::string> &indet_ring_names,
    const RingEnv &ring_environment,
    const CoeffVarMap &coefficients,
    int coefficient_count)
{
    ModelCheckResult result;
    ring current_ring = engine_ring();
    rChangeCurrRing(current_ring);

    auto describe = [&](const expr &atom)
    {
        std::string label = label_of(atom);
        if (label.size() > 80)
            label = label.substr(0, 77) + "...";
        return label;
    };

    auto contains_atom = [](const expr &root)
    {
        std::unordered_set<Z3_ast> seen;
        std::vector<expr> pending{root};
        while (!pending.empty())
        {
            const expr e = pending.back();
            pending.pop_back();
            if (!seen.insert((Z3_ast)e).second)
                continue;
            if (semantic_atom_moduli(e) >= 0)
                return true;
            if (e.is_quantifier())
                pending.push_back(e.body());
            else if (e.is_app())
                for (unsigned i = 0; i < e.num_args(); ++i)
                    pending.push_back(e.arg(i));
        }
        return false;
    };

    // Atoms under a binder or in a recursive definition cannot be evaluated
    // one model value at a time; a quantifier without atoms is Z3's own.
    std::vector<expr> atoms;
    {
        std::unordered_set<Z3_ast> seen;
        std::vector<expr> pending;
        for (unsigned i = 0; i < assertions.size(); ++i)
            pending.push_back(assertions[i]);
        while (!pending.empty())
        {
            const expr e = pending.back();
            pending.pop_back();
            if (!seen.insert((Z3_ast)e).second)
                continue;
            if (e.is_quantifier())
            {
                if (contains_atom(e.body()))
                {
                    result.reason =
                        "eqP/eqmod atoms under a quantifier are not checked";
                    return result;
                }
                continue;
            }
            if (!e.is_app())
                continue;
            if (e.decl().decl_kind() == Z3_OP_RECURSIVE)
            {
                result.reason = "recursive functions are not checked";
                return result;
            }
            if (semantic_atom_moduli(e) >= 0)
                atoms.push_back(e);
            for (unsigned i = 0; i < e.num_args(); ++i)
                pending.push_back(e.arg(i));
        }
    }

    // Whether some atom occurs inside the arguments of another, where its
    // model truth feeds the values the outer atom is checked with.
    bool nested = false;
    {
        std::unordered_set<Z3_ast> seen;
        std::vector<expr> pending;
        for (const expr &atom : atoms)
            for (unsigned i = 0; i < atom.num_args(); ++i)
                pending.push_back(atom.arg(i));
        while (!pending.empty() && !nested)
        {
            const expr e = pending.back();
            pending.pop_back();
            if (!seen.insert((Z3_ast)e).second || !e.is_app())
                continue;
            nested = semantic_atom_moduli(e) >= 0;
            for (unsigned i = 0; i < e.num_args(); ++i)
                pending.push_back(e.arg(i));
        }
    }

    struct Entry
    {
        expr atom;
        bool model_truth = false;
        bool semantic_truth = false;
        poly difference = nullptr;
        std::vector<poly> moduli;
    };
    std::vector<Entry> entries;
    struct EntriesOwner
    {
        std::vector<Entry> &entries;
        ring current_ring;
        ~EntriesOwner()
        {
            for (Entry &entry : entries)
            {
                delete_poly_if_nonnull(entry.difference, current_ring);
                delete_polys(entry.moduli, current_ring);
            }
        }
    } entries_owner{entries, current_ring};

    // With every constant valued by the model, the arguments become ground
    // Poly terms whose only symbols are PVar indeterminates. A model value can
    // be any exponent; lowering would abort the process above its limit.
    auto evaluate = [&](const expr &term, const std::string &tag)
    {
        const expr value = candidate.eval(term, true);
        std::unordered_set<Z3_ast> seen;
        std::vector<expr> pending{value};
        while (!pending.empty())
        {
            const expr e = pending.back();
            pending.pop_back();
            if (!e.is_app() || !seen.insert((Z3_ast)e).second)
                continue;
            if (is_ctor(e, "PPow", 2))
            {
                std::int64_t exponent = 0;
                if (e.arg(1).is_numeral_i64(exponent) &&
                    exponent > util::singular::lowering::max_pow_expand)
                    throw std::runtime_error(
                        "PPow exponent " + std::to_string(exponent) +
                        " exceeds the expansion limit");
            }
            for (unsigned i = 0; i < e.num_args(); ++i)
                pending.push_back(e.arg(i));
        }
        return polyterm_to_singular_poly(
            value, indets, indet_ring_names, ring_environment, coefficients,
            coefficient_count, tag);
    };
    entries.reserve(atoms.size());
    for (const expr &atom : atoms)
    {
        const std::string label = describe(atom);
        entries.push_back(Entry{atom});
        Entry &entry = entries.back();
        try
        {
            const expr truth = candidate.eval(atom, true);
            if (!truth.is_true() && !truth.is_false())
            {
                result.reason = label + " has no truth value in the model";
                return result;
            }
            entry.model_truth = truth.is_true();
            ScopedPolyOwner lhs(current_ring,
                                evaluate(atom.arg(0), label + "/LHS"));
            ScopedPolyOwner rhs(current_ring,
                                evaluate(atom.arg(1), label + "/RHS"));
            rhs.reset(poly_negate_owned(rhs.release(), current_ring));
            entry.difference =
                poly_add_owned(lhs.release(), rhs.release(), current_ring);
            for (unsigned i = 2; i < atom.num_args(); ++i)
            {
                poly modulus = evaluate(
                    atom.arg(i), label + "/MOD" + std::to_string(i - 1));
                if (modulus != nullptr)
                    entry.moduli.push_back(modulus);
            }
        }
        catch (const std::exception &error)
        {
            result.reason =
                label + " cannot be evaluated (" + error.what() + ")";
            return result;
        }
        // An eqP holds when the difference is zero; an eqmod atom also when
        // the difference lies in the ideal of its nonzero moduli.
        entry.semantic_truth = entry.difference == nullptr;
    }

    // One membership group per distinct set of moduli, as in final
    // validation.
    std::vector<util::singular::MembershipGroup> groups;
    std::vector<std::vector<std::size_t>> group_entries;
    for (std::size_t index = 0; index < entries.size(); ++index)
    {
        const Entry &entry = entries[index];
        if (entry.difference == nullptr || entry.moduli.empty())
            continue;
        std::size_t group = 0;
        for (; group < groups.size(); ++group)
        {
            const auto &generators = groups[group].extra_generators;
            if (generators.size() == entry.moduli.size() &&
                std::equal(generators.begin(), generators.end(),
                           entry.moduli.begin(),
                           [&](poly lhs, poly rhs)
                           { return same_poly(lhs, rhs, current_ring); }))
                break;
        }
        if (group == groups.size())
        {
            util::singular::MembershipGroup created;
            created.label = "eqmod-model-check";
            created.extra_generators = entry.moduli;
            groups.push_back(std::move(created));
            group_entries.emplace_back();
        }
        groups[group].targets.push_back(entry.difference);
        group_entries[group].push_back(index);
    }
    if (!groups.empty())
    {
        LOG_INFO(engine_log(), "singular",
                 "eqmod model check batch: atoms=" +
                     std::to_string(entries.size()) + " groups=" +
                     std::to_string(groups.size()));
        const util::singular::MembershipGroupBatchResult batch =
            run_membership_groups({}, groups, 0, false);
        accumulate_membership_group_timing(batch);
        if (batch.groups.size() != groups.size())
            throw std::runtime_error(
                "model check membership group count mismatch");
        for (std::size_t group = 0; group < groups.size(); ++group)
        {
            const auto &membership = batch.groups[group].membership;
            if (membership.size() != group_entries[group].size())
                throw std::runtime_error(
                    "model check membership result size mismatch");
            for (std::size_t i = 0; i < membership.size(); ++i)
                entries[group_entries[group][i]].semantic_truth =
                    membership[i];
        }
    }

    result.atoms = entries.size();
    std::vector<std::string> mismatches;
    for (const Entry &entry : entries)
        if (entry.model_truth != entry.semantic_truth)
            mismatches.push_back(
                describe(entry.atom) + " is " +
                (entry.model_truth ? "true" : "false") +
                " in the model but " +
                (entry.semantic_truth ? "true" : "false") +
                " for its values");
    if (mismatches.empty())
    {
        result.verified = true;
        return result;
    }

    std::string listed = mismatches.front();
    for (std::size_t i = 1; i < std::min<std::size_t>(mismatches.size(), 3);
         ++i)
        listed += "; " + mismatches[i];
    if (mismatches.size() > 3)
        listed += "; " + std::to_string(mismatches.size() - 3) + " more";

    // A wrong model truth need not falsify an assertion: an atom Z3 never
    // needed gets an arbitrary value, and a disjunction may hold through
    // another disjunct. Evaluating the assertions with every atom replaced by
    // its actual truth settles it, unless an atom is nested in another's
    // arguments, whose values the replacement would change.
    if (!nested)
    {
        context &ctx = candidate.ctx();
        expr_vector from(ctx);
        expr_vector to(ctx);
        for (const Entry &entry : entries)
        {
            from.push_back(entry.atom);
            to.push_back(ctx.bool_val(entry.semantic_truth));
        }
        bool holds = false;
        try
        {
            expr conjunction = z3::mk_and(assertions);
            holds = candidate.eval(conjunction.substitute(from, to), true)
                        .is_true();
        }
        catch (const std::exception &)
        {
            holds = false;
        }
        if (holds)
        {
            result.verified = true;
            result.reason = "the assertions hold with the actual truth of " +
                            std::to_string(mismatches.size()) +
                            " atom(s) the model has wrong: " + listed;
            return result;
        }
    }
    result.reason = listed;
    return result;
}

} // namespace eqmod
