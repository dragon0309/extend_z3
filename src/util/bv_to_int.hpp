#pragma once

#include <z3++.h>

#include <algorithm>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace util
{

// How a BV-to-Int conversion reads its bit-vector argument. Z3 parses both
// bv2int and bv2nat as ubv_to_int (Z3_OP_BV2INT); only sbv_to_int
// (Z3_OP_SBV2INT) is signed.
enum class BvToIntKind
{
    None,
    Unsigned,
    Signed
};

// Interpreted conversions are recognized by decl kind. An uninterpreted
// function that only carries a conversion name (the unit tests build them
// that way) is classified by its name; is_interpreted_bv_to_int tells the two
// apart where the meaning matters, e.g. mapping the zero bit-vector to 0.
inline BvToIntKind bv_to_int_kind(const z3::expr &e)
{
    if (!e.is_app() || e.num_args() != 1 || !e.get_sort().is_int() ||
        !e.arg(0).get_sort().is_bv())
        return BvToIntKind::None;
    switch (e.decl().decl_kind())
    {
    case Z3_OP_BV2INT:
        return BvToIntKind::Unsigned;
    case Z3_OP_SBV2INT:
        return BvToIntKind::Signed;
    default:
        break;
    }
    const std::string name = e.decl().name().str();
    if (name == "ubv_to_int" || name == "bv2nat" || name == "bv2int")
        return BvToIntKind::Unsigned;
    if (name == "sbv_to_int")
        return BvToIntKind::Signed;
    return BvToIntKind::None;
}

inline bool is_bv_to_int_app(const z3::expr &e)
{
    return bv_to_int_kind(e) != BvToIntKind::None;
}

inline bool is_interpreted_bv_to_int(const z3::func_decl &declaration)
{
    return declaration.decl_kind() == Z3_OP_BV2INT ||
           declaration.decl_kind() == Z3_OP_SBV2INT;
}

// 2^n as an Int numeral. Z3's own power of two Int numerals is Real-sorted,
// and bit-vector widths can exceed 63 bits.
inline z3::expr power_of_two(z3::context &context, unsigned n)
{
    std::string digits = "1";
    for (unsigned i = 0; i < n; ++i)
    {
        unsigned carry = 0;
        for (auto digit = digits.rbegin(); digit != digits.rend(); ++digit)
        {
            const unsigned doubled =
                2 * static_cast<unsigned>(*digit - '0') + carry;
            *digit = static_cast<char>('0' + doubled % 10);
            carry = doubled / 10;
        }
        if (carry != 0)
            digits.insert(digits.begin(), static_cast<char>('0' + carry));
    }
    return context.int_val(digits.c_str());
}

// The top bit of x as an Int, 0 or 1.
inline z3::expr msb_to_int(const z3::expr &x)
{
    const unsigned width = x.get_sort().bv_size();
    return z3::bv2int(x.extract(width - 1, width - 1), false);
}

// The signed value of x written through its unsigned view:
// sbv(x) = ubv(x) - 2^n * msb(x).
inline z3::expr signed_through_unsigned(const z3::expr &x)
{
    return z3::bv2int(x, false) -
           power_of_two(x.ctx(), x.get_sort().bv_size()) * msb_to_int(x);
}

// The bit-vector terms that one conversion reads signed (sbv_to_int) and
// another unsigned (ubv_to_int, which bv2nat and bv2int parse to), sorted by
// their SMT-LIB text. Quantifier bodies are searched too, but a term with a
// bound variable is left out: the same de Bruijn index in two quantifiers
// names two different variables.
inline std::vector<z3::expr> mixed_signedness_terms(
    const std::vector<z3::expr> &roots)
{
    auto has_bound_variable = [](const z3::expr &root)
    {
        std::unordered_set<Z3_ast> seen;
        std::vector<z3::expr> pending{root};
        while (!pending.empty())
        {
            const z3::expr e = pending.back();
            pending.pop_back();
            if (!seen.insert((Z3_ast)e).second)
                continue;
            if (e.is_var())
                return true;
            if (e.is_quantifier())
                pending.push_back(e.body());
            else if (e.is_app())
                for (unsigned i = 0; i < e.num_args(); ++i)
                    pending.push_back(e.arg(i));
        }
        return false;
    };

    // Bit 0: read unsigned; bit 1: read signed.
    std::unordered_map<Z3_ast, unsigned> readings;
    std::vector<z3::expr> arguments;
    std::unordered_set<Z3_ast> seen;
    std::vector<z3::expr> pending(roots.begin(), roots.end());
    while (!pending.empty())
    {
        const z3::expr e = pending.back();
        pending.pop_back();
        if (!seen.insert((Z3_ast)e).second)
            continue;
        if (e.is_quantifier())
        {
            pending.push_back(e.body());
            continue;
        }
        if (!e.is_app())
            continue;
        if (is_bv_to_int_app(e) && is_interpreted_bv_to_int(e.decl()))
        {
            const z3::expr argument = e.arg(0);
            auto [it, inserted] = readings.emplace((Z3_ast)argument, 0u);
            if (inserted)
                arguments.push_back(argument);
            it->second |= bv_to_int_kind(e) == BvToIntKind::Signed ? 2u : 1u;
        }
        for (unsigned i = 0; i < e.num_args(); ++i)
            pending.push_back(e.arg(i));
    }

    std::vector<std::pair<std::string, z3::expr>> mixed;
    for (const z3::expr &argument : arguments)
        if (readings.at((Z3_ast)argument) == 3u && !has_bound_variable(argument))
            mixed.emplace_back(argument.to_string(), argument);
    std::sort(mixed.begin(), mixed.end(),
              [](const auto &x, const auto &y) { return x.first < y.first; });
    std::vector<z3::expr> terms;
    terms.reserve(mixed.size());
    for (const auto &entry : mixed)
        terms.push_back(entry.second);
    return terms;
}

} // namespace util
