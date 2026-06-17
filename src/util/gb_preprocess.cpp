#include "util/gb_preprocess.hpp"

#include <algorithm>
#include <sstream>
#include <unordered_set>

#include "util/logger.hpp"

static std::string poly_to_string_local(poly p, const ring R)
{
    if (p == nullptr)
        return "0";
    char *s = p_String(p, R);
    std::string out = s ? std::string(s) : std::string("?");
    if (s)
        omFree(s);
    return out;
}

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

static poly poly_scale_coeffs_mod(poly p, const mpz_class &scale, const mpz_class &modulus, const ring R)
{
    if (p == nullptr)
        return nullptr;
    poly out = nullptr;
    for (poly t = p; t != nullptr; t = pNext(t))
    {
        mpz_class c = number_to_mpz(p_GetCoeff(t, R), R);
        c *= scale;
        if (modulus > 0)
        {
            c %= modulus;
            if (c < 0)
                c += modulus;
            if (c > modulus / 2)
                c -= modulus;
        }
        poly nt = poly_term_from_source(t, c, R);
        out = poly_add_owned_local(out, nt, R);
    }
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

static void replace_poly(poly &slot, poly next, const ring R)
{
    if (slot)
        p_Delete(&slot, R);
    slot = next;
}

static void normalize_poly_sign(poly &p, const ring R)
{
    if (p == nullptr)
        return;
    mpz_class lc = number_to_mpz(p_GetCoeff(p, R), R);
    if (lc < 0)
    {
        number neg1 = num_from_si_local(-1, R->cf);
        p = p_Mult_nn(p, neg1, R);
        n_Delete(&neg1, R->cf);
    }
}

struct SparseMonicReducer
{
    int var = 0;
    int degree = 0;
    mpz_class replacement = 0;
    std::string key;
};

static bool detect_sparse_monic_reducer(poly p, const ring R, SparseMonicReducer &out)
{
    if (p == nullptr || pNext(p) == nullptr || pNext(pNext(p)) != nullptr)
        return false;

    poly terms[2] = {p, pNext(p)};
    poly mono = nullptr;
    poly constant = nullptr;
    for (poly t : terms)
    {
        if (term_is_constant(t, R))
        {
            constant = t;
            continue;
        }

        int var = 0;
        int degree = 0;
        bool pure = true;
        for (int i = 1; i <= R->N; ++i)
        {
            int e = p_GetExp(t, i, R);
            if (e == 0)
                continue;
            if (var != 0)
            {
                pure = false;
                break;
            }
            var = i;
            degree = e;
        }
        if (!pure || var == 0 || degree <= 0)
            return false;
        mono = t;
    }

    if (mono == nullptr || constant == nullptr)
        return false;

    mpz_class lc = number_to_mpz(p_GetCoeff(mono, R), R);
    if (!(lc == 1 || lc == -1))
        return false;

    mpz_class c = number_to_mpz(p_GetCoeff(constant, R), R);
    out.var = 0;
    for (int i = 1; i <= R->N; ++i)
    {
        int e = p_GetExp(mono, i, R);
        if (e != 0)
        {
            out.var = i;
            out.degree = e;
            break;
        }
    }
    out.replacement = -c / lc;
    out.key = poly_to_string_local(p, R);
    return out.var != 0 && out.degree > 0;
}

static poly reduce_by_sparse_monic_reducers(poly p, const std::vector<SparseMonicReducer> &reducers, const ring R)
{
    if (p == nullptr || reducers.empty())
        return copy_poly_or_null_local(p, R);

    poly out = nullptr;
    for (poly t = p; t != nullptr; t = pNext(t))
    {
        mpz_class coeff = number_to_mpz(p_GetCoeff(t, R), R);
        std::vector<int> exps((std::size_t)R->N + 1, 0);
        for (int i = 1; i <= R->N; ++i)
            exps[(std::size_t)i] = p_GetExp(t, i, R);

        bool changed = true;
        while (changed)
        {
            changed = false;
            for (const auto &rr : reducers)
            {
                int &e = exps[(std::size_t)rr.var];
                if (e >= rr.degree)
                {
                    e -= rr.degree;
                    coeff *= rr.replacement;
                    changed = true;
                }
            }
        }

        if (coeff == 0)
            continue;
        poly nt = poly_from_mpz_local(coeff, R);
        for (int i = 1; i <= R->N; ++i)
            if (exps[(std::size_t)i] != 0)
                p_SetExp(nt, i, exps[(std::size_t)i], R);
        p_Setm(nt, R);
        out = poly_add_owned_local(out, nt, R);
    }
    return out;
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

static void dedup_generators(std::vector<poly> &gens, const ring R, GbPreprocessStats &stats)
{
    std::unordered_set<std::string> seen;
    std::vector<poly> out;
    out.reserve(gens.size());
    for (poly &g : gens)
    {
        if (g == nullptr)
            continue;
        normalize_poly_sign(g, R);
        const std::string key = poly_to_string_local(g, R);
        if (!seen.insert(key).second)
        {
            ++stats.duplicate_drops;
            p_Delete(&g, R);
            continue;
        }
        out.push_back(g);
    }
    gens.swap(out);
}

static void canonicalize_poly_mod_constant(poly &p, const mpz_class &d, const ring R, GbPreprocessStats &stats)
{
    // Sound only when the ideal still contains the constant generator <d>:
    // coefficients are normalized modulo d, and unit scaling is invertible modulo d.
    if (p == nullptr || d <= 0)
        return;
    std::string before = poly_to_string_local(p, R);
    poly q = poly_scale_coeffs_mod(p, 1, d, R);
    replace_poly(p, q, R);
    if (p != nullptr && before != poly_to_string_local(p, R))
        ++stats.coefficient_canonicalizations;

    if (p == nullptr)
        return;

    mpz_class lc = number_to_mpz(p_GetCoeff(p, R), R);
    mpz_class a = lc % d;
    if (a < 0)
        a += d;
    if (a == 0 || mpz_gcd_abs(a, d) != 1)
        return;

    mpz_class inv;
    if (mpz_invert(inv.get_mpz_t(), a.get_mpz_t(), d.get_mpz_t()) == 0)
        return;
    poly scaled = poly_scale_coeffs_mod(p, inv, d, R);
    replace_poly(p, scaled, R);
    ++stats.unit_normalizations;
}

void preprocess_groebner_inputs(std::vector<poly> &gens,
                                std::vector<poly> &targets,
                                const ring R,
                                const std::string &label,
                                GbPreprocessStats &stats,
                                util::Logger *logger)
{
    rChangeCurrRing(R);
    accumulate_poly_stats(gens, R, stats.gens_before, stats.terms_before, stats.coeff_abs_before);

    mpz_class d = 0;
    std::vector<poly> non_constants;
    non_constants.reserve(gens.size());
    for (poly &g : gens)
    {
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
    }
    gens.swap(non_constants);

    stats.constant_gcd = d;
    if (d == 1)
    {
        for (poly &g : gens)
            delete_poly_if_nonnull_local(g, R);
        gens.clear();
        gens.push_back(poly_from_si_local(1, R));
    }
    else if (d > 0)
    {
        // Keep <d> in the generators. Later mod/unit normalizations rely on this invariant.
        gens.push_back(poly_from_mpz_local(d, R));
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
                mpz_class shared = mpz_gcd_abs(content, d);
                mpz_class c_unit = content / shared;
                if (c_unit > 1 && mpz_gcd_abs(c_unit, d) == 1)
                {
                    poly q = poly_divide_coeffs_exact(g, c_unit, R);
                    replace_poly(g, q, R);
                    ++stats.content_divisions;
                }
            }
            canonicalize_poly_mod_constant(g, d, R, stats);
        }
        else
        {
            normalize_poly_sign(g, R);
        }
    }

    std::vector<SparseMonicReducer> reducers;
    for (poly g : gens)
    {
        SparseMonicReducer rr;
        if (detect_sparse_monic_reducer(g, R, rr))
            reducers.push_back(rr);
    }
    stats.monic_reducers = (int)reducers.size();

    if (!reducers.empty())
    {
        std::unordered_set<std::string> reducer_keys;
        for (const auto &rr : reducers)
            reducer_keys.insert(rr.key);

        for (poly &g : gens)
        {
            if (g == nullptr)
                continue;
            mpz_class c;
            if (d > 0 && poly_is_nonzero_constant(g, R, c))
            {
                if (c < 0)
                    c = -c;
                if (c == d)
                    continue;
            }
            if (reducer_keys.count(poly_to_string_local(g, R)) != 0)
                continue;
            std::string before = poly_to_string_local(g, R);
            poly q = reduce_by_sparse_monic_reducers(g, reducers, R);
            replace_poly(g, q, R);
            if (g == nullptr || before != poly_to_string_local(g, R))
                ++stats.monic_reductions;
            if (d > 0)
                canonicalize_poly_mod_constant(g, d, R, stats);
            else
                normalize_poly_sign(g, R);
        }

        for (poly &t : targets)
        {
            if (t == nullptr)
                continue;
            std::string before = poly_to_string_local(t, R);
            poly q = reduce_by_sparse_monic_reducers(t, reducers, R);
            replace_poly(t, q, R);
            if (t == nullptr || before != poly_to_string_local(t, R))
                ++stats.monic_reductions;
            if (d > 0)
                canonicalize_poly_mod_constant(t, d, R, stats);
        }
    }
    else if (d > 0)
    {
        for (poly &t : targets)
            canonicalize_poly_mod_constant(t, d, R, stats);
    }

    dedup_generators(gens, R, stats);
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
            << " ; coeff_mod=" << stats.coefficient_canonicalizations
            << " ; unit_norm=" << stats.unit_normalizations
            << " ; monic_reducers=" << stats.monic_reducers
            << " ; monic_reductions=" << stats.monic_reductions
            << " ; dup_drop=" << stats.duplicate_drops;
        LOG_INFO(*logger, "singular", oss.str());
    }
}
