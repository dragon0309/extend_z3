#pragma once

#include <z3++.h>

#include <cstddef>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

namespace util::eqmod
{

using AstSlotMap = std::unordered_map<Z3_ast, std::size_t>;

inline void require_preallocated_qvar_slots(
    std::size_t p1_atom_count,
    const std::vector<std::string> &p1_qvars,
    const std::vector<std::vector<z3::expr>> &atoms,
    const std::vector<std::vector<std::vector<std::string>>> &qvars)
{
    if (p1_qvars.size() != p1_atom_count)
        throw std::runtime_error(
            "eqmodP1: incomplete preallocated qvar table");
    for (unsigned family = 2; family <= 4; ++family)
    {
        if (atoms.size() <= family || qvars.size() <= family ||
            qvars[family].size() != atoms[family].size())
            throw std::runtime_error(
                "eqmodP" + std::to_string(family) +
                ": incomplete preallocated qvar table");
        for (std::size_t atom = 0; atom < atoms[family].size(); ++atom)
            if (qvars[family][atom].size() != family)
                throw std::runtime_error(
                    "eqmodP" + std::to_string(family) +
                    ": invalid quotient-variable arity");
    }
}

inline void translate_atom_slots(
    z3::context &target,
    const std::vector<z3::expr> &source_p1,
    const std::vector<std::vector<z3::expr>> &source_n,
    std::vector<z3::expr> &translated_p1,
    AstSlotMap &p1_slots,
    std::vector<std::vector<z3::expr>> &translated_n,
    std::vector<AstSlotMap> &n_slots)
{
    translated_p1.clear();
    p1_slots.clear();
    translated_n.assign(5, {});
    n_slots.assign(5, {});

    translated_p1.reserve(source_p1.size());
    for (std::size_t index = 0; index < source_p1.size(); ++index)
    {
        const z3::expr &source = source_p1[index];
        translated_p1.emplace_back(
            target,
            Z3_translate((Z3_context)source.ctx(), (Z3_ast)source,
                         (Z3_context)target));
        if (!p1_slots.emplace((Z3_ast)translated_p1.back(), index).second)
            throw std::runtime_error(
                "fresh(eqmodP1): duplicate translated AST slot");
    }

    for (unsigned family = 2; family <= 4; ++family)
    {
        if (source_n.size() <= family)
            continue;
        translated_n[family].reserve(source_n[family].size());
        for (std::size_t index = 0; index < source_n[family].size(); ++index)
        {
            const z3::expr &source = source_n[family][index];
            translated_n[family].emplace_back(
                target,
                Z3_translate((Z3_context)source.ctx(), (Z3_ast)source,
                             (Z3_context)target));
            if (!n_slots[family]
                     .emplace((Z3_ast)translated_n[family].back(), index)
                     .second)
                throw std::runtime_error(
                    "fresh(eqmodP" + std::to_string(family) +
                    "): duplicate translated AST slot");
        }
    }
}

} // namespace util::eqmod
