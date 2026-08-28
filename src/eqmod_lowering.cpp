#include "eqmod_engine.hpp"

#include <algorithm>
#include <array>
#include <cstring>
#include <stdexcept>

#include "util/singular_poly.hpp"

using namespace z3;
using namespace util::singular::lowering;
using util::singular::copy_poly_or_null;
using util::singular::delete_poly_if_nonnull;
using util::singular::num_from_si;
using util::singular::poly_add_owned;
using util::singular::poly_from_mpz;
using util::singular::poly_negate_owned;
using util::singular::poly_sub_product_clone;
using util::singular::poly_to_string;
using util::singular::ScopedPolyOwner;

namespace eqmod
{
namespace
{

bool starts_with(const std::string &value, const char *prefix)
{
    const std::size_t size = std::strlen(prefix);
    return value.size() >= size && value.compare(0, size, prefix) == 0;
}

bool is_unsupported_poly_lowering_error(const std::string &message)
{
    static const std::array<const char *, 7> prefixes = {
        "Unsupported Poly term:",
        "expr_to_poly_anyring: unsupported op:",
        "PConst argument not Int:",
        "PVar expects a String literal:",
        "Unknown indet:",
        "Unknown opaque polynomial symbol:",
        "PPow exponent must be non-negative Int numeral:"};
    return std::any_of(prefixes.begin(), prefixes.end(),
                       [&](const char *prefix)
                       { return starts_with(message, prefix); });
}

bool extract_modulus_from_polyconst(const expr &term, mpz_class &out)
{
    if (!is_ctor(term, "PConst", 1))
        return false;
    expr value = term.arg(0);
    if (!(value.is_numeral() && value.get_sort().is_int()))
        return false;

    Z3_string text = Z3_get_numeral_string(
        (Z3_context)value.ctx(), (Z3_ast)value);
    mpz_class parsed;
    if (parsed.set_str(text, 10) != 0)
        return false;
    out = parsed;
    return true;
}

} // namespace
poly make_var_poly(RingEnv &environment, const std::string &name)
{
    ring current_ring = environment.R;
    rChangeCurrRing(current_ring);
    int variable = environment.ensure_var_idx(name);

    poly result = p_NSet(num_from_si(1, current_ring->cf), current_ring);
    p_SetExp(result, variable, 1, current_ring);
    p_Setm(result, current_ring);
    return result;
}

P1Compiled compile_p1(
    const expr &atom,
    const expr &A,
    const expr &B,
    const expr &modulus,
    const std::string &label,
    const IndetEnv &indets,
    const std::vector<std::string> &indet_ring_names,
    RingEnv &ring_environment,
    const CoeffVarMap &coefficients,
    int coefficient_count,
    const std::string &quotient_name,
    util::Logger &log)
{
    ring current_ring = ring_environment.R;
    rChangeCurrRing(current_ring);

    P1Compiled out(atom, A, B, modulus, quotient_name, current_ring);

    auto clear_partial = [&]()
    {
        destroy(out, current_ring);
    };

    try
    {
        ScopedPolyOwner lhs(
            current_ring,
            polyterm_to_singular_poly(
                A, indets, indet_ring_names, ring_environment, coefficients,
                coefficient_count, label + "/LHS"));
        ScopedPolyOwner rhs(
            current_ring,
            polyterm_to_singular_poly(
                B, indets, indet_ring_names, ring_environment, coefficients,
                coefficient_count, label + "/RHS"));
        rhs.reset(poly_negate_owned(rhs.release(), current_ring));
        out.D = poly_add_owned(lhs.release(), rhs.release(), current_ring);

        mpz_class constant;
        if (extract_modulus_from_polyconst(modulus, constant))
        {
            out.modulus_is_const = true;
            out.m_const = constant;
            out.M_poly = poly_from_mpz(constant, current_ring);
        }
        else
        {
            out.M_poly = polyterm_to_singular_poly(
                modulus, indets, indet_ring_names, ring_environment,
                coefficients, coefficient_count, label + "/MOD");
        }
        out.modulus_ok = true;
        out.U_poly = make_var_poly(ring_environment, quotient_name);
        out.true_gen = copy_poly_or_null(out.D, current_ring);
        if (out.M_poly)
        {
            poly next = poly_sub_product_clone(
                out.true_gen, out.U_poly, out.M_poly, current_ring);
            delete_poly_if_nonnull(out.true_gen, current_ring);
            out.true_gen = next;
        }
        out.valid = true;
    }
    catch (const std::exception &error)
    {
        clear_partial();
        if (!is_unsupported_poly_lowering_error(error.what()))
            throw;
        out.incomplete_reason = error.what();
        LOG_WARN(log, "singular", label +
                     ": algebraic lowering unsupported; atom kept as UF and "
                     "semantic validation marked incomplete: " +
                     out.incomplete_reason);
        return out;
    }

    LOG_INFO(log, "singular", label + " D(poly) = " +
                                  poly_to_string(out.D, current_ring));
    if (out.M_poly)
        LOG_INFO(log, "singular", label + " M(poly) = " +
                                      poly_to_string(out.M_poly, current_ring));
    if (out.true_gen)
        LOG_INFO(log, "singular", label + " true_gen(poly) = " +
                                      poly_to_string(out.true_gen, current_ring));
    return out;
}

NCompiled compile_n(
    const expr &atom,
    const std::string &label,
    const IndetEnv &indets,
    const std::vector<std::string> &indet_ring_names,
    RingEnv &ring_environment,
    const CoeffVarMap &coefficients,
    int coefficient_count,
    const std::vector<std::string> &quotient_names,
    util::Logger &log)
{
    ring current_ring = ring_environment.R;
    rChangeCurrRing(current_ring);

    const unsigned arity = atom.num_args() - 2;
    if (arity < 2 || arity > 4 || quotient_names.size() != arity)
        throw std::runtime_error(
            label + ": invalid eqmod arity/qvar allocation");

    const expr A = atom.arg(0);
    const expr B = atom.arg(1);
    std::vector<expr> modulus_terms;
    modulus_terms.reserve(arity);
    for (unsigned i = 0; i < arity; ++i)
        modulus_terms.push_back(atom.arg(i + 2));
    NCompiled out(atom, A, B, arity, std::move(modulus_terms),
                  quotient_names, current_ring);

    out.modulus_polys.reserve(arity);
    out.quotient_polys.reserve(arity);

    auto clear_partial = [&]()
    {
        destroy(out, current_ring);
    };

    try
    {
        ScopedPolyOwner lhs(
            current_ring,
            polyterm_to_singular_poly(
                A, indets, indet_ring_names, ring_environment, coefficients,
                coefficient_count, label + "/LHS"));
        ScopedPolyOwner rhs(
            current_ring,
            polyterm_to_singular_poly(
                B, indets, indet_ring_names, ring_environment, coefficients,
                coefficient_count, label + "/RHS"));
        rhs.reset(poly_negate_owned(rhs.release(), current_ring));
        out.D = poly_add_owned(lhs.release(), rhs.release(), current_ring);

        for (unsigned i = 0; i < arity; ++i)
        {
            out.modulus_polys.push_back(polyterm_to_singular_poly(
                out.modulus_terms[i], indets, indet_ring_names,
                ring_environment, coefficients, coefficient_count,
                label + "/MOD" + std::to_string(i + 1)));
            out.quotient_polys.push_back(
                make_var_poly(ring_environment, quotient_names[i]));
        }
        out.M1_poly = out.modulus_polys[0];
        out.M2_poly = out.modulus_polys[1];
        out.U1_poly = out.quotient_polys[0];
        out.U2_poly = out.quotient_polys[1];

        out.true_gen = copy_poly_or_null(out.D, current_ring);
        for (unsigned i = 0; i < arity; ++i)
        {
            if (!out.modulus_polys[i])
                continue;
            poly next = poly_sub_product_clone(
                out.true_gen, out.quotient_polys[i], out.modulus_polys[i],
                current_ring);
            delete_poly_if_nonnull(out.true_gen, current_ring);
            out.true_gen = next;
        }
        out.valid = true;
    }
    catch (const std::exception &error)
    {
        clear_partial();
        if (!is_unsupported_poly_lowering_error(error.what()))
            throw;
        out.incomplete_reason = error.what();
        LOG_WARN(log, "singular", label +
                     ": algebraic lowering unsupported; atom kept as UF and "
                     "semantic validation marked incomplete: " +
                     out.incomplete_reason);
        return out;
    }

    LOG_INFO(log, "singular", label + " D(poly) = " +
                                  poly_to_string(out.D, current_ring));
    for (unsigned i = 0; i < arity; ++i)
        LOG_INFO(log, "singular", label + " M" + std::to_string(i + 1) +
                                      "(poly) = " +
                                      poly_to_string(out.modulus_polys[i],
                                                     current_ring));
    LOG_INFO(log, "singular", label + " true_gen(poly) = " +
                                  poly_to_string(out.true_gen, current_ring));
    return out;
}

void destroy(P1Compiled &atom, ring current_ring)
{
    delete_poly_if_nonnull(atom.D, current_ring);
    delete_poly_if_nonnull(atom.M_poly, current_ring);
    delete_poly_if_nonnull(atom.U_poly, current_ring);
    delete_poly_if_nonnull(atom.true_gen, current_ring);
    atom.owner_ring = nullptr;
}

void destroy(NCompiled &atom, ring current_ring)
{
    delete_poly_if_nonnull(atom.D, current_ring);
    util::singular::delete_polys(atom.modulus_polys, current_ring);
    util::singular::delete_polys(atom.quotient_polys, current_ring);
    atom.M1_poly = atom.M2_poly = nullptr;
    atom.U1_poly = atom.U2_poly = nullptr;
    delete_poly_if_nonnull(atom.true_gen, current_ring);
    atom.owner_ring = nullptr;
}

} // namespace eqmod
