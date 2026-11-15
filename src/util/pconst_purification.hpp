#pragma once

#include <z3++.h>

#include <string>
#include <vector>

namespace util::purify
{

// A non-polynomial Int subterm taken out of a PConst.
struct Replacement
{
    z3::expr constant; // the fresh Int constant that now stands for the term
    z3::expr term;     // the subterm itself; (= constant term) is asserted
};

// Rewrites the argument of every PConst into a form the polynomial lowering
// accepts, so that the atom around it becomes a polynomial instead of a UF.
//
// Numerals, Int constants, bit-vector-to-Int conversions, +, -, unary minus,
// * and ^ with a non-negative numeral exponent are kept. Any other Int
// subterm (div, mod, ite, an Int-valued function, ...) is replaced by a fresh
// Int constant c, and (= c subterm) is appended to `assertions`. The same
// subterm always gets the same constant. Z3 keeps the meaning of the subterm
// through that equality; the ring sees only the variable c, so every proof
// Singular finds holds whatever value the subterm takes.
//
// Quantified formulas are left as they are, because a subterm inside them may
// mention a bound variable and cannot be named by a constant.
std::vector<Replacement> purify_pconst_arguments(
    z3::context &context, std::vector<z3::expr> &assertions);

// True for the name of a constant made by purify_pconst_arguments.
bool is_purification_constant_name(const std::string &name);

} // namespace util::purify
