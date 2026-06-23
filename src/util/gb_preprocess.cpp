#include "util/gb_preprocess.hpp"

#include <sstream>

#include "util/logger.hpp"

namespace util::gb
{

namespace
{

static number num_from_si_local(long v, const coeffs cf)
{
    mpz_t z;
    mpz_init_set_si(z, v);
    number n = n_InitMPZ(z, cf);
    mpz_clear(z);
    return n;
}

static poly poly_from_mpz_local(const mpz_class &v, const ring R)
{
    mpz_t z;
    mpz_init_set(z, v.get_mpz_t());
    number n = n_InitMPZ(z, R->cf);
    mpz_clear(z);
    return p_NSet(n, R);
}

static poly poly_from_si_local(long v, const ring R)
{
    return p_NSet(num_from_si_local(v, R->cf), R);
}

static poly copy_poly_or_null_local(poly p, const ring R)
{
    return p ? p_Copy(p, R) : nullptr;
}

static void delete_poly_if_nonnull_local(poly &p, const ring R)
{
    if (p)
        p_Delete(&p, R);
    p = nullptr;
}

static poly poly_add_owned_local(poly a, poly b, const ring R)
{
    if (!a)
        return b;
    if (!b)
        return a;
    return p_Add_q(a, b, R);
}

static mpz_class number_to_mpz(number n, const ring R)
{
    number nc = n_Copy(n, R->cf);
    mpz_t z;
    mpz_init(z);
    n_MPZ(z, nc, R->cf);
    mpz_class out(z);
    mpz_clear(z);
    n_Delete(&nc, R->cf);
    return out;
}

static mpz_class mpz_gcd_abs(mpz_class a, mpz_class b)
{
    if (a < 0)
        a = -a;
    if (b < 0)
        b = -b;
    mpz_class out;
    mpz_gcd(out.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return out;
}

static bool term_is_constant(poly t, const ring R)
{
    if (t == nullptr)
        return true;
    for (int i = 1; i <= R->N; ++i)
        if (p_GetExp(t, i, R) != 0)
            return false;
    return true;
}

static bool poly_is_nonzero_constant(poly p, const ring R, mpz_class &out)
{
    if (p == nullptr || pNext(p) != nullptr || !term_is_constant(p, R))
        return false;
    out = number_to_mpz(p_GetCoeff(p, R), R);
    return out != 0;
}

static int poly_term_count(poly p)
{
    int n = 0;
    for (poly t = p; t != nullptr; t = pNext(t))
        ++n;
    return n;
}

static mpz_class poly_coeff_abs_sum(poly p, const ring R)
{
    mpz_class out = 0;
    for (poly t = p; t != nullptr; t = pNext(t))
    {
        mpz_class c = number_to_mpz(p_GetCoeff(t, R), R);
        if (c < 0)
            c = -c;
        out += c;
    }
    return out;
}

static poly poly_term_from_source(poly src, const mpz_class &coeff, const ring R)
{
    if (coeff == 0)
        return nullptr;
    poly out = poly_from_mpz_local(coeff, R);
    for (int i = 1; i <= R->N; ++i)
    {
        int e = p_GetExp(src, i, R);
        if (e != 0)
            p_SetExp(out, i, e, R);
    }
    p_Setm(out, R);
    return out;
}

static poly poly_coeffs_mod(poly p, const mpz_class &modulus, const ring R, bool &changed)
{
    changed = false;
    if (p == nullptr)
        return nullptr;
    poly out = nullptr;
    for (poly t = p; t != nullptr; t = pNext(t))
    {
        const mpz_class original = number_to_mpz(p_GetCoeff(t, R), R);
        mpz_class c = original;
        if (modulus > 0)
        {
            c %= modulus;
            if (c < 0)
                c += modulus;
            if (c > modulus / 2)
                c -= modulus;
        }
        changed = changed || c != original;
        poly nt = poly_term_from_source(t, c, R);
        out = poly_add_owned_local(out, nt, R);
    }
    if (out != nullptr)
        p_Normalize(out, R);
    return out;
}

static poly poly_divide_coeffs_exact(poly p, const mpz_class &divisor, const ring R)
{
    if (p == nullptr)
        return nullptr;
    poly out = nullptr;
    for (poly t = p; t != nullptr; t = pNext(t))
    {
        mpz_class c = number_to_mpz(p_GetCoeff(t, R), R);
        if (c % divisor != 0)
        {
            if (out)
                p_Delete(&out, R);
            return copy_poly_or_null_local(p, R);
        }
        c /= divisor;
        poly nt = poly_term_from_source(t, c, R);
        out = poly_add_owned_local(out, nt, R);
    }
    if (out != nullptr)
        p_Normalize(out, R);
    return out;
}

static mpz_class poly_content(poly p, const ring R)
{
    mpz_class g = 0;
    for (poly t = p; t != nullptr; t = pNext(t))
    {
        mpz_class c = number_to_mpz(p_GetCoeff(t, R), R);
        if (c < 0)
            c = -c;
        if (c == 0)
            continue;
        g = (g == 0) ? c : mpz_gcd_abs(g, c);
    }
    return g;
}

static mpz_class coprime_content_divisor(const mpz_class &content, const mpz_class &d)
{
    if (content <= 1)
        return 1;
    if (mpz_gcd_abs(content, d) == 1)
        return content;

    // Select the largest divisor of content that is coprime to d by removing
    // every prime-power factor shared with d.
    mpz_class unit = content;
    while (unit > 1)
    {
        mpz_class shared = mpz_gcd_abs(unit, d);
        if (shared == 1)
            break;
        unit /= shared;
    }
    return unit > 1 ? unit : mpz_class(1);
}

static void replace_poly(poly &slot, poly next, const ring R)
{
    if (slot)
        p_Delete(&slot, R);
    slot = next;
}

static void accumulate_poly_stats(const std::vector<poly> &polys,
                                  const ring R,
                                  int &count,
                                  int &terms,
                                  mpz_class &coeff_abs)
{
    count = 0;
    terms = 0;
    coeff_abs = 0;
    for (poly p : polys)
    {
        if (p == nullptr)
            continue;
        ++count;
        terms += poly_term_count(p);
        coeff_abs += poly_coeff_abs_sum(p, R);
    }
}

static void compact_generators(std::vector<poly> &gens,
                               std::vector<int> *origins)
{
    std::vector<poly> out;
    std::vector<int> out_origins;
    out.reserve(gens.size());
    if (origins)
        out_origins.reserve(gens.size());
    for (std::size_t i = 0; i < gens.size(); ++i)
    {
        poly &g = gens[i];
        if (g == nullptr)
            continue;
        out.push_back(g);
        if (origins)
            out_origins.push_back(i < origins->size() ? (*origins)[i] : -1);
    }
    gens.swap(out);
    if (origins)
        origins->swap(out_origins);
}

static void canonicalize_poly_mod_constant(poly &p,
                                           const mpz_class &d,
                                           const ring R,
                                           GbPreprocessStats &stats)
{
    // Sound only when the ideal still contains the constant generator <d>.
    if (p == nullptr || d <= 0)
        return;
    bool changed = false;
    poly q = poly_coeffs_mod(p, d, R, changed);
    replace_poly(p, q, R);
    if (changed)
        ++stats.coefficient_canonicalizations;
}

} // namespace

void preprocess_groebner_inputs(std::vector<poly> &gens,
                                std::vector<poly> &targets,
                                const ring R,
                                const std::string &label,
                                GbPreprocessStats &stats,
                                util::Logger *logger,
                                std::vector<int> *gen_origins)
{
    stats = GbPreprocessStats{};
    rChangeCurrRing(R);
    if (gen_origins && gen_origins->size() != gens.size())
    {
        gen_origins->clear();
        gen_origins->reserve(gens.size());
        for (std::size_t i = 0; i < gens.size(); ++i)
            gen_origins->push_back((int)i);
    }

    accumulate_poly_stats(gens, R, stats.gens_before, stats.terms_before, stats.coeff_abs_before);

    mpz_class d = 0;
    std::vector<poly> non_constants;
    std::vector<int> non_constant_origins;
    non_constants.reserve(gens.size());
    if (gen_origins)
        non_constant_origins.reserve(gens.size());
    for (std::size_t i = 0; i < gens.size(); ++i)
    {
        poly &g = gens[i];
        if (g == nullptr)
            continue;
        mpz_class c;
        if (poly_is_nonzero_constant(g, R, c))
        {
            if (c < 0)
                c = -c;
            d = (d == 0) ? c : mpz_gcd_abs(d, c);
            ++stats.constants_merged;
            p_Delete(&g, R);
            continue;
        }
        non_constants.push_back(g);
        if (gen_origins)
            non_constant_origins.push_back(i < gen_origins->size() ? (*gen_origins)[i] : -1);
    }
    gens.swap(non_constants);
    if (gen_origins)
        gen_origins->swap(non_constant_origins);

    stats.constant_gcd = d;
    if (d == 1)
    {
        for (poly &g : gens)
            delete_poly_if_nonnull_local(g, R);
        gens.clear();
        if (gen_origins)
            gen_origins->clear();
        gens.push_back(poly_from_si_local(1, R));
        if (gen_origins)
            gen_origins->push_back(-1);
    }
    else if (d > 0)
    {
        // Keep <d> in the generators. Coefficient reduction modulo d relies on this invariant.
        gens.push_back(poly_from_mpz_local(d, R));
        if (gen_origins)
            gen_origins->push_back(-1);
    }

    for (poly &g : gens)
    {
        if (g == nullptr)
            continue;
        mpz_class c;
        if (d > 0 && poly_is_nonzero_constant(g, R, c))
            continue;

        if (d > 0)
        {
            mpz_class content = poly_content(g, R);
            if (content > 1)
            {
                mpz_class c_unit = coprime_content_divisor(content, d);
                if (c_unit > 1)
                {
                    poly q = poly_divide_coeffs_exact(g, c_unit, R);
                    replace_poly(g, q, R);
                    ++stats.content_divisions;
                }
            }
            canonicalize_poly_mod_constant(g, d, R, stats);
        }
    }

    if (d > 0)
    {
        for (poly &t : targets)
            canonicalize_poly_mod_constant(t, d, R, stats);
    }

    compact_generators(gens, gen_origins);
    for (poly &g : gens)
    {
        if (g != nullptr)
            p_Normalize(g, R);
    }
    for (poly &t : targets)
    {
        if (t != nullptr)
            p_Normalize(t, R);
    }
    accumulate_poly_stats(gens, R, stats.gens_after, stats.terms_after, stats.coeff_abs_after);

    if (logger)
    {
        std::ostringstream oss;
        oss << "[gb-preprocess] " << label
            << ": gens " << stats.gens_before << " -> " << stats.gens_after
            << " ; terms " << stats.terms_before << " -> " << stats.terms_after
            << " ; coeff_abs " << stats.coeff_abs_before.get_str() << " -> " << stats.coeff_abs_after.get_str()
            << " ; const_gcd=" << (d == 0 ? std::string("-") : d.get_str())
            << " ; content_div=" << stats.content_divisions
            << " ; coeff_mod=" << stats.coefficient_canonicalizations;
        LOG_INFO(*logger, "singular", oss.str());
    }
}

} // namespace util::gb
