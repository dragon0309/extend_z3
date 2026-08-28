#include "util/singular_lowering.hpp"

#include <z3.h>

#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <utility>

namespace util::singular
{

namespace lowering
{
namespace
{

constexpr std::int64_t max_pow_expand = 65536;

number num_from_z3_any(const z3::expr &value, coeffs coefficients)
{
    const Z3_string text = Z3_get_numeral_string(
        static_cast<Z3_context>(value.ctx()), static_cast<Z3_ast>(value));
    mpz_t integer;
    mpz_init(integer);
    if (mpz_set_str(integer, text, 10) != 0)
    {
        mpz_clear(integer);
        throw std::runtime_error(std::string("bad numeral: ") + text);
    }
    number result = n_InitMPZ(integer, coefficients);
    mpz_clear(integer);
    return result;
}

void collect_indets_rec(
    const z3::expr &value,
    std::unordered_set<std::string> &out)
{
    if (is_ctor(value, "PVar", 1))
    {
        std::string name;
        if (get_string_literal_smt(value.arg(0), name))
            out.insert(name);
    }
    if (!value.is_app())
        return;
    for (unsigned index = 0; index < value.num_args(); ++index)
        collect_indets_rec(value.arg(index), out);
}

void collect_raw_poly_symbols_rec(
    const z3::expr &value,
    std::unordered_set<std::string> &out)
{
    if (is_raw_poly_symbol(value))
    {
        out.insert(value.to_string());
        return;
    }
    if (!value.is_app())
        return;
    for (unsigned index = 0; index < value.num_args(); ++index)
        collect_raw_poly_symbols_rec(value.arg(index), out);
}

z3::expr z3_pow(z3::expr base, int exponent)
{
    if (exponent <= 0)
        return base.ctx().int_val(1);
    z3::expr result = base.ctx().int_val(1);
    while (exponent > 0)
    {
        if (exponent & 1)
            result = result * base;
        exponent >>= 1;
        if (exponent)
            base = base * base;
    }
    return result;
}

} // namespace

bool is_poly_sort(const z3::sort &value)
{
    if (!value.is_datatype())
        return false;
    const Z3_context context = static_cast<Z3_context>(value.ctx());
    const Z3_symbol symbol = Z3_get_sort_name(
        context, static_cast<Z3_sort>(value));
    const char *name = Z3_get_symbol_string(context, symbol);
    return name && std::string(name) == "Poly";
}

bool is_ctor(const z3::expr &value, const char *name, unsigned arity)
{
    return value.is_app() && value.decl().name().str() == name &&
           value.num_args() == arity;
}

bool get_int64_numeral(const z3::expr &value, std::int64_t &out)
{
    if (!(value.is_numeral() && value.get_sort().is_int()))
        return false;
    return Z3_get_numeral_int64(
        static_cast<Z3_context>(value.ctx()), static_cast<Z3_ast>(value),
        &out);
}

bool get_string_literal_smt(const z3::expr &value, std::string &out)
{
    if (!Z3_is_string_sort(
            static_cast<Z3_context>(value.ctx()),
            static_cast<Z3_sort>(value.get_sort())))
        return false;

    std::string text = value.to_string();
    if (text.size() < 2 || text.front() != '"' || text.back() != '"')
        return false;
    text = text.substr(1, text.size() - 2);

    std::string decoded;
    decoded.reserve(text.size());
    for (std::size_t index = 0; index < text.size(); ++index)
    {
        if (text[index] == '\\' && index + 1 < text.size() &&
            (text[index + 1] == '\\' || text[index + 1] == '"'))
        {
            decoded.push_back(text[index + 1]);
            ++index;
        }
        else
        {
            decoded.push_back(text[index]);
        }
    }
    out = std::move(decoded);
    return true;
}

bool is_raw_poly_symbol(const z3::expr &value)
{
    return value.is_const() && !value.is_numeral() &&
           is_poly_sort(value.get_sort());
}

std::string raw_poly_symbol_key(const z3::expr &value)
{
    return "PolySymbol:" + value.to_string();
}

bool contains_raw_poly_symbol(const z3::expr &value)
{
    if (is_raw_poly_symbol(value))
        return true;
    if (!value.is_app())
        return false;
    for (unsigned index = 0; index < value.num_args(); ++index)
        if (contains_raw_poly_symbol(value.arg(index)))
            return true;
    return false;
}

std::vector<std::string> collect_all_indets(
    const std::vector<z3::expr> &roots)
{
    std::unordered_set<std::string> names;
    for (const z3::expr &root : roots)
        collect_indets_rec(root, names);
    std::vector<std::string> result(names.begin(), names.end());
    std::sort(result.begin(), result.end());
    return result;
}

std::vector<std::string> collect_all_raw_poly_symbols(
    const std::vector<z3::expr> &roots)
{
    std::unordered_set<std::string> symbols;
    for (const z3::expr &root : roots)
        collect_raw_poly_symbols_rec(root, symbols);
    std::vector<std::string> result(symbols.begin(), symbols.end());
    std::sort(result.begin(), result.end());
    return result;
}

bool is_bv_to_int_app(const z3::expr &value)
{
    if (!value.is_app() || !value.get_sort().is_int() ||
        value.num_args() != 1 || !value.arg(0).get_sort().is_bv())
        return false;
#ifdef Z3_OP_BV2INT
    if (value.decl().decl_kind() == Z3_OP_BV2INT)
        return true;
#endif
    const std::string name = value.decl().name().str();
    return name == "ubv_to_int" || name == "sbv_to_int" ||
           name == "bv2nat" || name == "bv2int";
}

std::string coeff_base_pretty_name(const z3::expr &value)
{
    if (is_bv_to_int_app(value))
    {
        const z3::expr bv = value.arg(0);
        if (bv.is_const() && !bv.is_numeral())
            return bv.decl().name().str();
        return "bv2int";
    }
    if (value.is_const() && !value.is_numeral())
        return value.decl().name().str();
    return value.to_string();
}

void collect_coeff_bases_rec(
    const z3::expr &value,
    std::unordered_set<Z3_ast> &out)
{
    if (value.get_sort().is_int())
    {
        if ((value.is_const() && !value.is_numeral()) ||
            is_bv_to_int_app(value))
            out.insert(static_cast<Z3_ast>(value));
    }
    if (!value.is_app())
        return;
    for (unsigned index = 0; index < value.num_args(); ++index)
        collect_coeff_bases_rec(value.arg(index), out);
}

RingEnv::~RingEnv()
{
    if (R)
    {
        rDelete(R);
        R = nullptr;
    }
    for (char *name : name_buf)
        std::free(name);
    name_buf.clear();
}

void RingEnv::build(coeffs coefficients,
                    const std::vector<std::string> &variables,
                    rRingOrder_t)
{
    int variable_count = static_cast<int>(variables.size());
    if (variable_count == 0)
        variable_count = 1;

    name_buf.clear();
    name_buf.reserve(variable_count);
    var_to_idx.clear();
    if (!variables.empty())
    {
        for (std::size_t index = 0; index < variables.size(); ++index)
        {
            name_buf.push_back(::strdup(variables[index].c_str()));
            var_to_idx[variables[index]] = static_cast<int>(index) + 1;
        }
    }
    else
    {
        name_buf.push_back(::strdup("k"));
        var_to_idx["k"] = 1;
    }

    if (R)
    {
        rDelete(R);
        R = nullptr;
    }
    ord_heap = nullptr;
    block0_heap = nullptr;
    block1_heap = nullptr;
    wvhdl_heap = nullptr;
    ord_size = 3;
    ord_heap = static_cast<rRingOrder_t *>(
        omAlloc(ord_size * sizeof(rRingOrder_t)));
    block0_heap = static_cast<int *>(omAlloc0(ord_size * sizeof(int)));
    block1_heap = static_cast<int *>(omAlloc0(ord_size * sizeof(int)));
    ord_heap[0] = ringorder_lp;
    ord_heap[1] = ringorder_C;
    ord_heap[2] = static_cast<rRingOrder_t>(0);
    block0_heap[0] = 1;
    block1_heap[0] = variable_count;

    R = rDefault(coefficients, variable_count, name_buf.data(), ord_size,
                 ord_heap, block0_heap, block1_heap, wvhdl_heap);
    if (!R)
        throw std::runtime_error("rDefault returned null ring.");
    rComplete(R);
    rChangeCurrRing(R);
}

int RingEnv::ensure_var_idx(const std::string &ring_name) const
{
    const auto found = var_to_idx.find(ring_name);
    if (found == var_to_idx.end())
        throw std::runtime_error(
            "RingEnv: unknown ring variable: " + ring_name);
    return found->second;
}

void bind_ring_indices(CoeffVarMap &mapping,
                       const RingEnv &environment,
                       const std::vector<std::string> &indet_ring_names,
                       unsigned split_indet_count)
{
    mapping.coeff_ring_index.resize(mapping.ring_names.size());
    for (std::size_t index = 0; index < mapping.ring_names.size(); ++index)
        mapping.coeff_ring_index[index] =
            environment.ensure_var_idx(mapping.ring_names[index]);

    if (split_indet_count > indet_ring_names.size())
        throw std::runtime_error(
            "bind_ring_indices: split indeterminate count out of range");
    mapping.indet_ring_index.resize(split_indet_count);
    for (std::size_t index = 0; index < split_indet_count; ++index)
        mapping.indet_ring_index[index] =
            environment.ensure_var_idx(indet_ring_names[index]);
}

poly expr_to_poly_anyring(const z3::expr &value,
                          const RingEnv &environment,
                          const CoeffVarMap &mapping)
{
    ring R = environment.R;
    if (!R)
        throw std::runtime_error("expr_to_poly_anyring: ring is null");
    rChangeCurrRing(R);

    if (value.is_numeral())
        return p_NSet(num_from_z3_any(value, R->cf), R);

    if (is_bv_to_int_app(value) ||
        (value.is_const() && value.get_sort().is_int()))
    {
        const auto found = mapping.base_to_index.find(static_cast<Z3_ast>(value));
        if (found == mapping.base_to_index.end())
            throw std::runtime_error(
                "expr_to_poly_anyring: base missing from cmap: " +
                value.to_string());
        const int variable = environment.ensure_var_idx(
            mapping.ring_names[found->second]);
        poly result = poly_one(R);
        p_SetExp(result, variable, 1, R);
        p_Setm(result, R);
        return result;
    }
    if (value.is_const())
        throw std::runtime_error(
            "expr_to_poly_anyring: non-int const: " + value.to_string());
    if (!value.is_app())
        throw std::runtime_error(
            "expr_to_poly_anyring: unsupported expr: " + value.to_string());

    switch (value.decl().decl_kind())
    {
    case Z3_OP_ADD:
    {
        poly result = nullptr;
        for (unsigned index = 0; index < value.num_args(); ++index)
            result = poly_add_owned(
                result,
                expr_to_poly_anyring(value.arg(index), environment, mapping),
                R);
        return result;
    }
    case Z3_OP_SUB:
        if (value.num_args() == 1)
            return poly_negate_owned(
                expr_to_poly_anyring(value.arg(0), environment, mapping), R);
        if (value.num_args() == 2)
            return poly_add_owned(
                expr_to_poly_anyring(value.arg(0), environment, mapping),
                poly_negate_owned(
                    expr_to_poly_anyring(value.arg(1), environment, mapping),
                    R),
                R);
        throw std::runtime_error("expr_to_poly_anyring: SUB >2 args");
    case Z3_OP_UMINUS:
        return poly_negate_owned(
            expr_to_poly_anyring(value.arg(0), environment, mapping), R);
    case Z3_OP_MUL:
    {
        if (value.num_args() == 0)
            return poly_one(R);
        poly result = expr_to_poly_anyring(value.arg(0), environment, mapping);
        for (unsigned index = 1; index < value.num_args(); ++index)
            result = p_Mult_q(
                result,
                expr_to_poly_anyring(value.arg(index), environment, mapping),
                R);
        return result;
    }
    case Z3_OP_POWER:
    {
        if (value.num_args() != 2 ||
            !(value.arg(1).is_numeral() &&
              value.arg(1).get_sort().is_int()))
            throw std::runtime_error(
                "expr_to_poly_anyring: POWER exponent must be Int numeral");
        mpz_t exponent_value;
        mpz_init(exponent_value);
        const Z3_string exponent_text = Z3_get_numeral_string(
            static_cast<Z3_context>(value.ctx()),
            static_cast<Z3_ast>(value.arg(1)));
        if (mpz_set_str(exponent_value, exponent_text, 10) != 0 ||
            mpz_sgn(exponent_value) < 0 ||
            !mpz_fits_ulong_p(exponent_value))
        {
            mpz_clear(exponent_value);
            throw std::runtime_error(
                "expr_to_poly_anyring: invalid exponent numeral");
        }
        unsigned long exponent = mpz_get_ui(exponent_value);
        mpz_clear(exponent_value);
        if (exponent == 0)
            return poly_one(R);

        poly base = expr_to_poly_anyring(value.arg(0), environment, mapping);
        poly result = poly_one(R);
        while (exponent > 0)
        {
            if (exponent & 1)
            {
                poly next = poly_mul_clone(result, base, R);
                delete_poly_if_nonnull(result, R);
                result = next;
            }
            exponent >>= 1;
            if (exponent)
            {
                poly next = poly_mul_clone(base, base, R);
                delete_poly_if_nonnull(base, R);
                base = next;
            }
        }
        delete_poly_if_nonnull(base, R);
        return result;
    }
    default:
        throw std::runtime_error(
            "expr_to_poly_anyring: unsupported op: " +
            value.decl().name().str());
    }
}

poly polyterm_to_singular_poly(
    const z3::expr &value,
    const IndetEnv &indets,
    const std::vector<std::string> &indet_ring_names,
    const RingEnv &environment,
    const CoeffVarMap &mapping,
    int coefficient_count,
    const std::string &tag)
{
    ring R = environment.R;
    if (!R)
        throw std::runtime_error("polyterm_to_singular_poly: ring is null");
    rChangeCurrRing(R);

    if (is_ctor(value, "PConst", 1))
    {
        if (!value.arg(0).get_sort().is_int())
            throw std::runtime_error(
                "PConst argument not Int: " + value.to_string());
        return expr_to_poly_anyring(value.arg(0), environment, mapping);
    }
    if (is_ctor(value, "PVar", 1))
    {
        std::string raw;
        if (!get_string_literal_smt(value.arg(0), raw))
            throw std::runtime_error(
                "PVar expects a String literal: " + value.to_string());
        const auto found = indets.idx.find("PVar:" + raw);
        if (found == indets.idx.end())
            throw std::runtime_error("Unknown indet: PVar:" + raw);
        poly result = poly_one(R);
        p_SetExp(result,
                 environment.ensure_var_idx(indet_ring_names[found->second]),
                 1, R);
        p_Setm(result, R);
        return result;
    }
    if (is_raw_poly_symbol(value))
    {
        const auto found = indets.idx.find(raw_poly_symbol_key(value));
        if (found == indets.idx.end())
            throw std::runtime_error(
                "Unknown opaque polynomial symbol: " + value.to_string());
        poly result = poly_one(R);
        p_SetExp(result,
                 environment.ensure_var_idx(indet_ring_names[found->second]),
                 1, R);
        p_Setm(result, R);
        return result;
    }

    auto lower_child = [&](unsigned index) {
        return polyterm_to_singular_poly(
            value.arg(index), indets, indet_ring_names, environment, mapping,
            coefficient_count, tag);
    };
    if (is_ctor(value, "PNeg", 1))
        return poly_negate_owned(lower_child(0), R);
    if (is_ctor(value, "PAdd", 2))
    {
        ScopedPolyOwner lhs(R, lower_child(0));
        ScopedPolyOwner rhs(R, lower_child(1));
        return poly_add_owned(lhs.release(), rhs.release(), R);
    }
    if (is_ctor(value, "PSub", 2))
    {
        ScopedPolyOwner lhs(R, lower_child(0));
        ScopedPolyOwner rhs(R, lower_child(1));
        rhs.reset(poly_negate_owned(rhs.release(), R));
        return poly_add_owned(lhs.release(), rhs.release(), R);
    }
    if (is_ctor(value, "PMul", 2))
    {
        ScopedPolyOwner lhs(R, lower_child(0));
        ScopedPolyOwner rhs(R, lower_child(1));
        return p_Mult_q(lhs.release(), rhs.release(), R);
    }
    if (is_ctor(value, "PPow", 2))
    {
        std::int64_t exponent = 0;
        if (!get_int64_numeral(value.arg(1), exponent) || exponent < 0)
            throw std::runtime_error(
                "PPow exponent must be non-negative Int numeral: " +
                value.to_string());
        if (exponent == 0)
            return poly_one(R);
        if (exponent > max_pow_expand)
        {
            std::cerr << "[fatal] PPow exponent too large: k=" << exponent
                      << " > MAX_POW_EXPAND=" << max_pow_expand
                      << " (refuse to expand; abort)\n";
            std::exit(2);
        }
        poly base = lower_child(0);
        if (exponent == 1)
            return base;
        poly result = poly_one(R);
        std::uint64_t remaining = static_cast<std::uint64_t>(exponent);
        while (remaining > 0)
        {
            if (remaining & 1)
            {
                poly next = poly_mul_clone(result, base, R);
                delete_poly_if_nonnull(result, R);
                result = next;
            }
            remaining >>= 1;
            if (remaining)
            {
                poly next = poly_mul_clone(base, base, R);
                delete_poly_if_nonnull(base, R);
                base = next;
            }
        }
        delete_poly_if_nonnull(base, R);
        return result;
    }
    throw std::runtime_error("Unsupported Poly term: " + value.to_string());
}

ideal ideal_from_polys(const std::vector<poly> &generators,
                       const RingEnv &environment)
{
    rChangeCurrRing(environment.R);
    ideal result = idInit(static_cast<int>(generators.size()), 1);
    for (std::size_t index = 0; index < generators.size(); ++index)
        result->m[static_cast<int>(index)] = generators[index];
    return result;
}

std::size_t IndetKeyHash::operator()(const IndetKey &key) const noexcept
{
    std::size_t hash = 1469598103934665603ull;
    for (int exponent : key.exponents)
        hash ^= static_cast<std::size_t>(exponent) + 0x9e3779b9 +
                (hash << 6) + (hash >> 2);
    return hash;
}

std::unordered_map<IndetKey, poly, IndetKeyHash>
split_by_indets(poly value,
                const CoeffVarMap &mapping,
                int indet_count,
                const RingEnv &environment)
{
    ring R = environment.R;
    rChangeCurrRing(R);
    const int coefficient_count =
        static_cast<int>(mapping.coeff_ring_index.size());
    if (coefficient_count != static_cast<int>(mapping.ring_names.size()))
        throw std::runtime_error(
            "split_by_indets: coeff_ring_index not bound");
    if (indet_count != static_cast<int>(mapping.indet_ring_index.size()))
        throw std::runtime_error(
            "split_by_indets: indet_ring_index size mismatch");

    std::unordered_map<IndetKey, poly, IndetKeyHash> result;
    for (poly term = value; term; term = pNext(term))
    {
        IndetKey key;
        key.exponents.assign(static_cast<std::size_t>(indet_count), 0);
        for (int index = 0; index < indet_count; ++index)
            key.exponents[static_cast<std::size_t>(index)] = p_GetExp(
                term, mapping.indet_ring_index[static_cast<std::size_t>(index)],
                R);

        poly coefficient = p_NSet(n_Copy(p_GetCoeff(term, R), R->cf), R);
        for (int index = 0; index < coefficient_count; ++index)
        {
            const int variable =
                mapping.coeff_ring_index[static_cast<std::size_t>(index)];
            const int exponent = p_GetExp(term, variable, R);
            if (exponent)
                p_SetExp(coefficient, variable, exponent, R);
        }
        p_Setm(coefficient, R);
        const auto found = result.find(key);
        if (found == result.end())
            result.emplace(std::move(key), coefficient);
        else
            found->second = poly_add_owned(found->second, coefficient, R);
    }
    return result;
}

z3::expr coeff_poly_to_z3_expr(z3::context &context,
                               poly value,
                               ring R,
                               const CoeffVarMap &mapping)
{
    if (!value)
        return context.int_val(0);
    z3::expr result = context.int_val(0);
    for (poly term = value; term; term = pNext(term))
    {
        const std::string coefficient =
            number_to_decimal_string(p_GetCoeff(term, R), R);
        z3::expr product = context.int_val(coefficient.c_str());
        for (std::size_t index = 0;
             index < mapping.coeff_ring_index.size(); ++index)
        {
            const int exponent = p_GetExp(
                term, mapping.coeff_ring_index[index], R);
            if (exponent)
                product = product * z3_pow(mapping.z3_bases[index], exponent);
        }
        result = result + product;
    }
    return result.simplify();
}

} // namespace lowering
} // namespace util::singular
