#pragma once

#include <z3++.h>

#include "util/singular_poly.hpp"

#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace util::singular
{

namespace lowering
{

bool is_poly_sort(const z3::sort &value);
bool is_ctor(const z3::expr &value, const char *name, unsigned arity);
bool get_int64_numeral(const z3::expr &value, std::int64_t &out);
bool get_string_literal_smt(const z3::expr &value, std::string &out);

bool is_raw_poly_symbol(const z3::expr &value);
std::string raw_poly_symbol_key(const z3::expr &value);
bool contains_raw_poly_symbol(const z3::expr &value);
std::vector<std::string> collect_all_indets(
    const std::vector<z3::expr> &roots);
std::vector<std::string> collect_all_raw_poly_symbols(
    const std::vector<z3::expr> &roots);

bool is_bv_to_int_app(const z3::expr &value);
std::string coeff_base_pretty_name(const z3::expr &value);
void collect_coeff_bases_rec(
    const z3::expr &value,
    std::unordered_set<Z3_ast> &out);

struct IndetEnv
{
    // PVar entries come first; raw (Poly Int) symbols follow. Only the former
    // participate in coefficient splitting.
    std::vector<std::string> names;
    std::unordered_map<std::string, unsigned> idx;
    unsigned split_indet_count = 0;
};

struct CoeffVarMap
{
    std::vector<z3::expr> z3_bases;
    std::vector<std::string> ring_names;
    std::unordered_map<Z3_ast, unsigned> base_to_index;
    std::vector<int> coeff_ring_index;
    std::vector<int> indet_ring_index;
};

struct RingEnv
{
    ring R = nullptr;
    std::vector<char *> name_buf;
    std::unordered_map<std::string, int> var_to_idx;
    int ord_size = 0;
    rRingOrder_t *ord_heap = nullptr;
    int *block0_heap = nullptr;
    int *block1_heap = nullptr;
    int **wvhdl_heap = nullptr;

    RingEnv() = default;
    ~RingEnv();
    RingEnv(const RingEnv &) = delete;
    RingEnv &operator=(const RingEnv &) = delete;

    void build(coeffs coefficients,
               const std::vector<std::string> &variables,
               rRingOrder_t order = ringorder_lp);
    int ensure_var_idx(const std::string &ring_name) const;
};

void bind_ring_indices(CoeffVarMap &mapping,
                       const RingEnv &environment,
                       const std::vector<std::string> &indet_ring_names,
                       unsigned split_indet_count);

poly expr_to_poly_anyring(const z3::expr &value,
                          const RingEnv &environment,
                          const CoeffVarMap &mapping);

poly polyterm_to_singular_poly(
    const z3::expr &value,
    const IndetEnv &indets,
    const std::vector<std::string> &indet_ring_names,
    const RingEnv &environment,
    const CoeffVarMap &mapping,
    int coefficient_count,
    const std::string &tag);

ideal ideal_from_polys(const std::vector<poly> &generators,
                       const RingEnv &environment);

struct IndetKey
{
    std::vector<int> exponents;
    bool operator==(const IndetKey &other) const
    {
        return exponents == other.exponents;
    }
};

struct IndetKeyHash
{
    std::size_t operator()(const IndetKey &key) const noexcept;
};

std::unordered_map<IndetKey, poly, IndetKeyHash>
split_by_indets(poly value,
                const CoeffVarMap &mapping,
                int indet_count,
                const RingEnv &environment);

z3::expr coeff_poly_to_z3_expr(z3::context &context,
                               poly value,
                               ring R,
                               const CoeffVarMap &mapping);

} // namespace lowering
} // namespace util::singular
