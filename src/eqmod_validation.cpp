#include "eqmod_engine.hpp"

#include <algorithm>
#include <stdexcept>

#include "util/singular_poly.hpp"

using namespace z3;
using util::singular::delete_polys;

namespace eqmod
{

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
            LOG_INFO(engine_log(), "singular",
                     "[eqmodP" + std::to_string(family) +
                         "] final validation incomplete: " + label_of(atom) +
                         " reason=" + skip_reason);
            return;
        }

        std::vector<poly> generators = modulus_polys;
        generators.insert(generators.end(), assignments.begin(),
                          assignments.end());
        tasks.push_back({atom, A, B, modulus_terms, difference,
                         std::move(generators), std::move(assignments),
                         family, assigned, difference == nullptr});
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
    return true;
}

} // namespace eqmod
