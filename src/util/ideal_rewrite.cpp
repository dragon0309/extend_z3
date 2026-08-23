#include "util/ideal_rewrite.hpp"

#include <algorithm>
#include <functional>
#include <sstream>
#include <string>
#include <unordered_map>
#include <utility>

#include "util/fmt_duration.hpp"
#include "util/singular_poly.hpp"

namespace util::ideal_rewrite
{
namespace
{

using clk = std::chrono::steady_clock;
constexpr std::size_t kMaxRounds = 100;

struct Rule
{
    int variable = 0;
    poly rhs = nullptr;
    std::size_t source = 0;
};

poly variable_poly(int variable, ring R)
{
    poly result = util::singular::poly_one(R);
    p_SetExp(result, variable, 1, R);
    p_Setm(result, R);
    return result;
}

bool is_standalone_linear_variable(poly term, int &variable, ring R)
{
    variable = 0;
    for (int i = 1; i <= R->N; ++i)
    {
        const int exponent = p_GetExp(term, i, R);
        if (exponent == 0)
            continue;
        if (exponent != 1 || variable != 0)
            return false;
        variable = i;
    }
    return variable != 0;
}

bool variable_occurs_outside_term(poly polynomial,
                                  poly selected_term,
                                  int variable,
                                  ring R)
{
    for (poly term = polynomial; term != nullptr; term = pNext(term))
        if (term != selected_term && p_GetExp(term, variable, R) != 0)
            return true;
    return false;
}

bool extract_rule(poly generator, std::size_t source, ring R, Rule &out)
{
    poly selected_term = nullptr;
    int selected_variable = 0;
    std::string selected_name;
    for (poly term = generator; term != nullptr; term = pNext(term))
    {
        int variable = 0;
        if (!is_standalone_linear_variable(term, variable, R))
            continue;
        const number coefficient = p_GetCoeff(term, R);
        if (!n_IsOne(coefficient, R->cf) && !n_IsMOne(coefficient, R->cf))
            continue;
        if (variable_occurs_outside_term(generator, term, variable, R))
            continue;
        const std::string name =
            R->names[variable - 1] ? R->names[variable - 1] : std::string();
        if (selected_term == nullptr || name < selected_name)
        {
            selected_term = term;
            selected_variable = variable;
            selected_name = name;
        }
    }
    if (selected_term == nullptr)
        return false;

    // generator = x + rest => x = -rest = x-generator
    // generator = -x + rest => x = rest = generator+x
    poly variable = variable_poly(selected_variable, R);
    poly rhs = p_Copy(generator, R);
    if (n_IsOne(p_GetCoeff(selected_term, R), R->cf))
        rhs = p_Add_q(variable, p_Neg(rhs, R), R);
    else
        rhs = p_Add_q(rhs, variable, R);

    out.variable = selected_variable;
    out.rhs = rhs;
    out.source = source;
    return true;
}

poly power_copy(poly base, int exponent, ring R)
{
    poly result = util::singular::poly_one(R);
    for (int i = 0; i < exponent; ++i)
    {
        if (base == nullptr)
        {
            util::singular::delete_poly_if_nonnull(result, R);
            return nullptr;
        }
        result = p_Mult_q(result, p_Copy(base, R), R);
    }
    return result;
}

poly substitute_copy(poly input, int variable, poly rhs, ring R, bool &changed)
{
    changed = false;
    poly result = nullptr;
    for (poly term = input; term != nullptr; term = pNext(term))
    {
        const int exponent = p_GetExp(term, variable, R);
        changed = changed || exponent != 0;

        poly monomial = p_NSet(n_Copy(p_GetCoeff(term, R), R->cf), R);
        for (int i = 1; i <= R->N; ++i)
        {
            const int term_exponent = i == variable ? 0 : p_GetExp(term, i, R);
            if (term_exponent != 0)
                p_SetExp(monomial, i, term_exponent, R);
        }
        p_Setm(monomial, R);

        poly replacement = power_copy(rhs, exponent, R);
        poly rewritten_term = replacement == nullptr
                                  ? nullptr
                                  : p_Mult_q(monomial, replacement, R);
        if (replacement == nullptr)
            util::singular::delete_poly_if_nonnull(monomial, R);
        if (rewritten_term != nullptr)
            result = result == nullptr
                         ? rewritten_term
                         : p_Add_q(result, rewritten_term, R);
    }
    if (result != nullptr)
        p_Normalize(result, R);
    return result;
}

bool substitute_owned(poly &value, const Rule &rule, ring R)
{
    if (value == nullptr)
        return false;
    bool changed = false;
    poly rewritten = substitute_copy(value, rule.variable, rule.rhs, R, changed);
    util::singular::delete_poly_if_nonnull(value, R);
    value = rewritten;
    return changed;
}

bool rhs_uses_variable(poly rhs, int variable, ring R)
{
    for (poly term = rhs; term != nullptr; term = pNext(term))
        if (p_GetExp(term, variable, R) != 0)
            return true;
    return false;
}

bool topo_sort_rules(const std::vector<Rule> &rules,
                     ring R,
                     std::vector<std::size_t> &order)
{
    std::unordered_map<int, std::size_t> by_variable;
    for (std::size_t i = 0; i < rules.size(); ++i)
        by_variable.emplace(rules[i].variable, i);

    std::vector<unsigned char> color(rules.size(), 0);
    std::function<bool(std::size_t)> visit = [&](std::size_t index) {
        if (color[index] == 2)
            return true;
        if (color[index] == 1)
            return false;
        color[index] = 1;
        for (const auto &[variable, dependency] : by_variable)
            if (rhs_uses_variable(rules[index].rhs, variable, R) &&
                !visit(dependency))
                return false;
        color[index] = 2;
        order.push_back(index);
        return true;
    };

    for (std::size_t i = 0; i < rules.size(); ++i)
        if (!visit(i))
            return false;
    return true;
}

void compose_rules(std::vector<Rule> &rules,
                   const std::vector<std::size_t> &order,
                   ring R)
{
    std::vector<std::size_t> composed;
    composed.reserve(order.size());
    for (std::size_t index : order)
    {
        for (std::size_t dependency : composed)
            substitute_owned(rules[index].rhs, rules[dependency], R);
        composed.push_back(index);
    }
}

void delete_rules(std::vector<Rule> &rules, ring R)
{
    for (Rule &rule : rules)
        util::singular::delete_poly_if_nonnull(rule.rhs, R);
    rules.clear();
}

bool compact_and_deduplicate(std::vector<poly> &generators,
                             ring R,
                             IdealRewriteStats &stats)
{
    std::vector<poly> compact;
    compact.reserve(generators.size());
    bool changed = false;
    for (poly &generator : generators)
    {
        if (generator == nullptr)
        {
            ++stats.zero_generators_dropped;
            changed = true;
            continue;
        }
        const bool duplicate = std::any_of(
            compact.begin(), compact.end(), [&](poly existing) {
                return p_EqualPolys(existing, generator, R);
            });
        if (duplicate)
        {
            util::singular::delete_poly_if_nonnull(generator, R);
            ++stats.duplicate_generators_dropped;
            changed = true;
            continue;
        }
        compact.push_back(generator);
        generator = nullptr;
    }
    generators.swap(compact);
    return changed;
}

} // namespace

void rewrite_inputs(std::vector<poly> &owned_generators,
                    std::vector<poly> &owned_targets,
                    ring R,
                    const std::string &label,
                    IdealRewriteStats &stats,
                    util::Logger *log)
{
    const auto started = clk::now();
    stats.input_generators = owned_generators.size();
    stats.input_targets = owned_targets.size();
    if (R == nullptr)
        return;
    rChangeCurrRing(R);

    compact_and_deduplicate(owned_generators, R, stats);
    for (std::size_t round = 0;
         round < kMaxRounds && !owned_generators.empty();
         ++round)
    {
        std::vector<Rule> rules;
        std::unordered_map<int, std::size_t> first_by_variable;
        try
        {
            for (std::size_t i = 0; i < owned_generators.size(); ++i)
            {
                Rule candidate;
                if (!extract_rule(owned_generators[i], i, R, candidate))
                    continue;
                if (!first_by_variable.emplace(candidate.variable, rules.size()).second)
                {
                    util::singular::delete_poly_if_nonnull(candidate.rhs, R);
                    continue;
                }
                rules.push_back(candidate);
            }
            if (rules.empty())
                break;

            std::vector<std::size_t> order;
            if (!topo_sort_rules(rules, R, order))
            {
                // Match the assertion pipeline's functional worklist fallback:
                // consume one safe rule, then extract again from the residuals.
                for (std::size_t i = 1; i < rules.size(); ++i)
                    util::singular::delete_poly_if_nonnull(rules[i].rhs, R);
                rules.resize(1);
                order.assign(1, 0);
                ++stats.cycle_worklist_steps;
            }
            else
            {
                compose_rules(rules, order, R);
            }

            std::vector<bool> consumed(owned_generators.size(), false);
            for (const Rule &rule : rules)
                consumed[rule.source] = true;

            std::vector<poly> residuals;
            residuals.reserve(owned_generators.size() - rules.size());
            for (std::size_t i = 0; i < owned_generators.size(); ++i)
            {
                poly value = owned_generators[i];
                owned_generators[i] = nullptr;
                if (consumed[i])
                {
                    util::singular::delete_poly_if_nonnull(value, R);
                    continue;
                }
                bool rewritten = false;
                for (std::size_t rule_index : order)
                    rewritten = substitute_owned(value, rules[rule_index], R) || rewritten;
                stats.generators_rewritten += rewritten ? 1 : 0;
                residuals.push_back(value);
            }
            owned_generators.swap(residuals);

            for (poly &target : owned_targets)
            {
                bool rewritten = false;
                for (std::size_t rule_index : order)
                    rewritten = substitute_owned(target, rules[rule_index], R) || rewritten;
                stats.targets_rewritten += rewritten ? 1 : 0;
            }

            stats.rules_extracted += rules.size();
            ++stats.rounds;
            compact_and_deduplicate(owned_generators, R, stats);
            delete_rules(rules, R);
        }
        catch (...)
        {
            delete_rules(rules, R);
            throw;
        }
    }

    stats.output_generators = owned_generators.size();
    stats.elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
        clk::now() - started);
    if (log)
    {
        std::ostringstream message;
        message << "[monic-variable-elimination] " << label
                << ": generators=" << stats.input_generators
                << "->" << stats.output_generators
                << " targets=" << stats.input_targets
                << " rounds=" << stats.rounds
                << " rules=" << stats.rules_extracted
                << " rewritten_generators=" << stats.generators_rewritten
                << " rewritten_targets=" << stats.targets_rewritten
                << " zero_dropped=" << stats.zero_generators_dropped
                << " duplicate_dropped=" << stats.duplicate_generators_dropped
                << " cycle_worklist_steps=" << stats.cycle_worklist_steps
                << " elapsed=" << util::fmt_duration(stats.elapsed);
        LOG_INFO(*log, "singular", message.str());
    }
}

} // namespace util::ideal_rewrite
