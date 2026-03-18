#include <z3++.h>
#include <z3.h>
#include <Singular/libsingular.h>
#include <gmpxx.h>
#include <limits>
#include <gmp.h>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <cctype>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include <sstream>

#include "util/fmt_duration.hpp"
#include "util/logger.hpp"

using namespace z3;
using clk = std::chrono::steady_clock;

static bool SHOW_MODEL = true;
static bool SINGULAR_VERBOSE = true;
static bool PRINT_RING_DETAIL = false;
static bool PRINT_FIXED_ALL = true;
static bool PRINT_PROPAGATE = true;
static bool PRINT_POW_STATS = true;
static bool PRINT_POW_BASE = true;
static bool singular_initialized = false;
static constexpr int64_t MAX_POW_EXPAND = 65536;
static size_t LOG_EXPR_MAXLEN = 20000000;
static Logger g_log;

static bool ORDER = true;
static bool ENV = false;
static bool SKIP_ALL_TRUE = false; // unused now
static bool ENABLE_ALL_FALSE = true;
static bool ENABLE_ALL_TRUE = true;
static bool ENABLE_MIXED = true;

static void init_singular()
{
    if (!singular_initialized)
    {
        const char *envp = std::getenv("SINGULAR_PATH");
        const char *default_path = ENV ? "/home/yfz309/Singular/build/Singular/Singular"
                                       : "/usr/bin/Singular";

        const char *path = envp ? envp : default_path;
        siInit((char *)path);
        singular_initialized = true;
    }
}

static void dump_ring(const ring R)
{
    if (!PRINT_RING_DETAIL)
        return;

    LOG_INFO(g_log, "singular", "Current ring:");
    rWrite(R);
    std::cout << "\n";
}

static void print_ideal(const char *label, ideal I, const ring R)
{
    if (!SINGULAR_VERBOSE)
        return;

    std::cout << "[INFO ][singular  ] " << label << " = {";
    bool first = true;
    for (int i = 0; i < I->ncols; ++i)
    {
        if (I->m[i] == nullptr)
            continue;
        if (!first)
            std::cout << ", ";
        char *s = p_String(I->m[i], R);
        std::cout << s;
        omFree(s);
        first = false;
    }
    std::cout << "}\n";
}

static std::string poly_to_string(poly p, const ring R)
{
    if (p == nullptr)
        return "0";
    char *s = p_String(p, R);
    std::string out = s ? std::string(s) : std::string("?");
    if (s)
        omFree(s);
    return out;
}

// ---------------- SMT2 injection (Poly + eqP + eqmodP1) ----------------
static const char *k_poly_prelude = R"PRE(
(declare-datatype Poly
  (par (T)
    ((PConst (const_c T))
     (PVar   (var_name String))
     (PNeg   (neg_p (Poly T)))
     (PAdd   (add_l (Poly T)) (add_r (Poly T)))
     (PSub   (sub_l (Poly T)) (sub_r (Poly T)))
     (PMul   (mul_l (Poly T)) (mul_r (Poly T)))
     (PPow   (pow_base (Poly T)) (pow_k Int)))))

(declare-fun eqP ((Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP1 ((Poly Int) (Poly Int) (Poly Int)) Bool)

; kept for future
(declare-fun eqmodP2 ((Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP3 ((Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP4 ((Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
)PRE";

static std::string read_file_all(const char *filename)
{
    std::ifstream ifs(filename, std::ios::in | std::ios::binary);
    if (!ifs)
        throw std::runtime_error(std::string("cannot open file: ") + filename);
    std::string s;
    ifs.seekg(0, std::ios::end);
    s.resize((size_t)ifs.tellg());
    ifs.seekg(0, std::ios::beg);
    if (!s.empty())
        ifs.read(&s[0], (std::streamsize)s.size());
    return s;
}

static bool contains_poly_decl(const std::string &s)
{
    if (s.find("(declare-datatype Poly") != std::string::npos)
        return true;
    if (s.find("(declare-datatypes") != std::string::npos && s.find("Poly") != std::string::npos)
        return true;
    return false;
}

static std::string inject_after_setlogic(const std::string &raw, const std::string &ins)
{
    size_t pos = raw.find("(set-logic");
    if (pos == std::string::npos)
        return ins + std::string("\n") + raw;

    size_t line_end = raw.find('\n', pos);
    if (line_end == std::string::npos)
        return raw + std::string("\n") + ins;

    std::string out;
    out.reserve(raw.size() + ins.size() + 8);
    out.append(raw, 0, line_end + 1);
    out.append(ins);
    out.push_back('\n');
    out.append(raw, line_end + 1, std::string::npos);
    return out;
}

static std::string inject_poly_eqP_eqmodP_if_missing(const std::string &raw)
{
    if (contains_poly_decl(raw))
        return raw;
    return inject_after_setlogic(raw, k_poly_prelude);
}

static std::vector<expr> parse_smt2_assertions(context &ctx, const std::string &smt2_script)
{
    Z3_context z3c = (Z3_context)ctx;
    Z3_ast_vector v = Z3_parse_smtlib2_string(
        z3c, smt2_script.c_str(),
        0, nullptr, nullptr,
        0, nullptr, nullptr);

    Z3_error_code ec = Z3_get_error_code(z3c);
    if (ec != Z3_OK)
        throw z3::exception(Z3_get_error_msg(z3c, ec));

    unsigned n = Z3_ast_vector_size(z3c, v);
    std::vector<expr> out;
    out.reserve(n);
    for (unsigned i = 0; i < n; ++i)
    {
        Z3_ast a = Z3_ast_vector_get(z3c, v, i);
        out.emplace_back(ctx, a);
    }
    return out;
}

// ---------------- helpers ----------------
static bool is_poly_sort(const sort &s)
{
    if (!s.is_datatype())
        return false;
    Z3_context c = (Z3_context)s.ctx();
    Z3_symbol sym = Z3_get_sort_name(c, (Z3_sort)s);
    const char *nm = Z3_get_symbol_string(c, sym);
    return nm && std::string(nm) == "Poly";
}

static bool is_ctor(const expr &e, const char *name, unsigned arity)
{
    return e.is_app() && e.decl().name().str() == name && e.num_args() == arity;
}

static bool get_int64_numeral(const expr &e, int64_t &out)
{
    if (!(e.is_numeral() && e.get_sort().is_int()))
        return false;
    return Z3_get_numeral_int64((Z3_context)e.ctx(), (Z3_ast)e, &out);
}

static bool get_string_literal_smt(const expr &e, std::string &out)
{
    if (!Z3_is_string_sort((Z3_context)e.ctx(), (Z3_sort)e.get_sort()))
        return false;

    std::string s = e.to_string();
    if (s.size() < 2 || s.front() != '"' || s.back() != '"')
        return false;
    s = s.substr(1, s.size() - 2);

    std::string r;
    r.reserve(s.size());
    for (size_t i = 0; i < s.size(); ++i)
    {
        if (s[i] == '\\' && i + 1 < s.size())
        {
            char n = s[i + 1];
            if (n == '\\' || n == '"')
            {
                r.push_back(n);
                ++i;
                continue;
            }
        }
        r.push_back(s[i]);
    }
    out = r;
    return true;
}

static std::string sanitize_ring_var_base(const std::string &s)
{
    std::string r;
    r.reserve(s.size());
    for (char ch : s)
    {
        if (std::isalnum((unsigned char)ch) || ch == '_')
            r.push_back(ch);
        else
            r.push_back('_');
    }
    if (r.empty() || std::isdigit((unsigned char)r[0]))
        r = "v_" + r;
    return r;
}

static std::string make_unique_name(const std::string &base, std::unordered_set<std::string> &used)
{
    if (!used.count(base))
    {
        used.insert(base);
        return base;
    }
    for (int k = 1;; ++k)
    {
        std::string cand = base + "_u" + std::to_string(k);
        if (!used.count(cand))
        {
            used.insert(cand);
            return cand;
        }
    }
}

// ---------------- collectors ----------------
static void collect_eqP_rec(const expr &e, std::vector<expr> &atoms)
{
    if (!e.is_app())
        return;
    if (e.decl().name().str() == "eqP" && e.num_args() == 2)
    {
        atoms.push_back(e);
        return;
    }
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_eqP_rec(e.arg(i), atoms);
}

static void collect_eqmodP1_rec(const expr &e, std::vector<expr> &atoms)
{
    if (!e.is_app())
        return;
    if (e.decl().name().str() == "eqmodP1" && e.num_args() == 3)
    {
        atoms.push_back(e);
        return;
    }
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_eqmodP1_rec(e.arg(i), atoms);
}

static void collect_indets_rec(const expr &e, std::unordered_set<std::string> &S)
{
    if (is_ctor(e, "PVar", 1))
    {
        std::string nm;
        if (get_string_literal_smt(e.arg(0), nm))
            S.insert(nm);
    }

    if (!e.is_app())
        return;
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_indets_rec(e.arg(i), S);
}

static std::vector<std::string> collect_all_indets(const std::vector<expr> &roots)
{
    std::unordered_set<std::string> S;
    for (auto &r : roots)
        collect_indets_rec(r, S);
    std::vector<std::string> out(S.begin(), S.end());
    std::sort(out.begin(), out.end());
    return out;
}

// ---------------- BV->Int detector + coefficient-base collector ----------------
static bool is_bv_to_int_app(const z3::expr &e)
{
    if (!e.is_app())
        return false;
    if (!e.get_sort().is_int())
        return false;
    if (e.num_args() != 1)
        return false;
    if (!e.arg(0).get_sort().is_bv())
        return false;

#ifdef Z3_OP_BV2INT
    if (e.decl().decl_kind() == Z3_OP_BV2INT)
        return true;
#endif

    const std::string n = e.decl().name().str();
    return (n == "ubv_to_int" || n == "sbv_to_int" || n == "bv2nat" || n == "bv2int");
}

static std::string coeff_base_pretty_name(const z3::expr &e)
{
    if (is_bv_to_int_app(e))
    {
        z3::expr bv = e.arg(0);
        if (bv.is_const() && !bv.is_numeral())
            return bv.decl().name().str();
        return std::string("bv2int");
    }

    if (e.is_const() && !e.is_numeral())
        return e.decl().name().str();

    return e.to_string();
}

static void collect_coeff_bases_rec(const z3::expr &e, std::unordered_set<Z3_ast> &S)
{
    if (e.get_sort().is_int())
    {
        if (e.is_const() && !e.is_numeral())
            S.insert((Z3_ast)e);
        else if (is_bv_to_int_app(e))
            S.insert((Z3_ast)e);
    }

    if (!e.is_app())
        return;
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_coeff_bases_rec(e.arg(i), S);
}

// ---------------- Indet environment ----------------
struct IndetEnv
{
    std::vector<std::string> names;
    std::unordered_map<std::string, unsigned> idx;
};

// ---------------- Coeff var mapping ----------------
struct CoeffVarMap
{
    std::vector<z3::expr> z3_bases;
    std::vector<std::string> ring_names;
    std::unordered_map<Z3_ast, unsigned> base_to_index;
};

// ---------------- Singular: number helpers ----------------
static number num_from_z3_any(const expr &e, const coeffs cf)
{
    Z3_string zs = Z3_get_numeral_string((Z3_context)e.ctx(), (Z3_ast)e);
    mpz_t v;
    mpz_init(v);
    if (mpz_set_str(v, zs, 10) != 0)
    {
        mpz_clear(v);
        throw std::runtime_error(std::string("bad numeral: ") + zs);
    }
    number n = n_InitMPZ(v, cf);
    mpz_clear(v);
    return n;
}

static number num_from_si(long v, const coeffs cf)
{
    mpz_t z;
    mpz_init_set_si(z, v);
    number n = n_InitMPZ(z, cf);
    mpz_clear(z);
    return n;
}

static poly poly_from_mpz(const mpz_class &v, const ring R)
{
    mpz_t z;
    mpz_init_set(z, v.get_mpz_t());
    number n = n_InitMPZ(z, R->cf);
    mpz_clear(z);
    return p_NSet(n, R);
}

static poly poly_from_si(long v, const ring R)
{
    return p_NSet(num_from_si(v, R->cf), R);
}

static poly poly_mul_clone(poly a, poly b, const ring R)
{
    poly ac = p_Copy(a, R), bc = p_Copy(b, R);
    return p_Mult_q(ac, bc, R);
}

static std::string number_to_decimal_string(number n, const ring R)
{
    number nc = n_Copy(n, R->cf);
    poly p = p_NSet(nc, R);
    char *s = p_String(p, R);
    std::string out(s);
    omFree(s);
    if (p)
        p_Delete(&p, R);
    return out;
}

// ---------------- Ring environment ----------------
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

    ~RingEnv()
    {
        if (R)
        {
            rDelete(R);
            R = nullptr;
        }

        for (char *p : name_buf)
            free(p);
        name_buf.clear();

        ord_heap = nullptr;
        block0_heap = nullptr;
        block1_heap = nullptr;
        wvhdl_heap = nullptr;
        ord_size = 0;
    }

    void build(coeffs cf,
               const std::vector<std::string> &base_vars,
               rRingOrder_t /*order_ignored*/ = ringorder_lp)
    {
        init_singular();

        int N = (int)base_vars.size();
        if (N == 0)
            N = 1;

        name_buf.clear();
        name_buf.reserve(N);
        var_to_idx.clear();

        if (!base_vars.empty())
        {
            for (int i = 0; i < (int)base_vars.size(); ++i)
            {
                name_buf.push_back(strdup(base_vars[i].c_str()));
                var_to_idx[base_vars[i]] = i + 1;
            }
        }
        else
        {
            name_buf.push_back(strdup("k"));
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
        ord_size = 0;

        ord_size = 3;
        ord_heap = (rRingOrder_t *)omAlloc(ord_size * sizeof(rRingOrder_t));
        block0_heap = (int *)omAlloc0(ord_size * sizeof(int));
        block1_heap = (int *)omAlloc0(ord_size * sizeof(int));
        wvhdl_heap = nullptr;

        ord_heap[0] = ringorder_dp;
        ord_heap[1] = ringorder_C;
        ord_heap[2] = (rRingOrder_t)0;

        block0_heap[0] = 1;
        block1_heap[0] = N;

        R = rDefault(cf, N, name_buf.data(), ord_size, ord_heap, block0_heap, block1_heap, wvhdl_heap);
        if (!R)
            throw std::runtime_error("rDefault returned null ring.");

        rComplete(R);
        rChangeCurrRing(R);
        dump_ring(R);
    }

    int ensure_var_idx(const std::string &ring_name)
    {
        auto it = var_to_idx.find(ring_name);
        if (it != var_to_idx.end())
            return it->second;

        throw std::runtime_error("RingEnv: unknown ring variable: " + ring_name);
    }
};

// ---------------- Z3 Int expr -> Singular poly ----------------
static poly expr_to_poly_anyring(const expr &e, RingEnv &RE, const CoeffVarMap &cmap)
{
    ring R = RE.R;
    if (!R)
        throw std::runtime_error("expr_to_poly_anyring: ring is null");
    rChangeCurrRing(R);

    if (e.is_numeral())
    {
        number bn = num_from_z3_any(e, R->cf);
        return p_NSet(bn, R);
    }

    if (is_bv_to_int_app(e))
    {
        auto it = cmap.base_to_index.find((Z3_ast)e);
        if (it == cmap.base_to_index.end())
            throw std::runtime_error("expr_to_poly_anyring: bv2int base missing from cmap: " + e.to_string());

        std::string ringnm = cmap.ring_names[it->second];
        int vi = RE.ensure_var_idx(ringnm);

        poly p = p_NSet(num_from_si(1, R->cf), R);
        p_SetExp(p, vi, 1, R);
        p_Setm(p, R);
        return p;
    }

    if (e.is_const())
    {
        if (!e.get_sort().is_int())
            throw std::runtime_error("expr_to_poly_anyring: non-int const: " + e.to_string());

        auto it = cmap.base_to_index.find((Z3_ast)e);
        if (it == cmap.base_to_index.end())
            throw std::runtime_error("expr_to_poly_anyring: Int symbol missing from cmap: " + e.to_string());

        std::string ringnm = cmap.ring_names[it->second];
        int vi = RE.ensure_var_idx(ringnm);

        poly p = p_NSet(num_from_si(1, R->cf), R);
        p_SetExp(p, vi, 1, R);
        p_Setm(p, R);
        return p;
    }

    if (!e.is_app())
        throw std::runtime_error("expr_to_poly_anyring: unsupported expr: " + e.to_string());

    switch (e.decl().decl_kind())
    {
    case Z3_OP_ADD:
    {
        poly res = nullptr;
        for (unsigned i = 0; i < e.num_args(); ++i)
        {
            poly pi = expr_to_poly_anyring(e.arg(i), RE, cmap);
            res = p_Add_q(res, pi, R);
        }
        return res;
    }
    case Z3_OP_SUB:
    {
        if (e.num_args() == 1)
        {
            poly p1 = expr_to_poly_anyring(e.arg(0), RE, cmap);
            number m1 = num_from_si(-1, R->cf);
            poly r = p_Mult_nn(p1, m1, R);
            n_Delete(&m1, R->cf);
            return r;
        }
        if (e.num_args() == 2)
        {
            poly p1 = expr_to_poly_anyring(e.arg(0), RE, cmap);
            poly p2 = expr_to_poly_anyring(e.arg(1), RE, cmap);
            number m1 = num_from_si(-1, R->cf);
            poly p2n = p_Mult_nn(p2, m1, R);
            n_Delete(&m1, R->cf);
            return p_Add_q(p1, p2n, R);
        }
        throw std::runtime_error("expr_to_poly_anyring: SUB >2 args");
    }
    case Z3_OP_UMINUS:
    {
        poly p1 = expr_to_poly_anyring(e.arg(0), RE, cmap);
        number m1 = num_from_si(-1, R->cf);
        poly r = p_Mult_nn(p1, m1, R);
        n_Delete(&m1, R->cf);
        return r;
    }
    case Z3_OP_MUL:
    {
        if (e.num_args() == 0)
            return poly_from_si(1, R);
        poly res = expr_to_poly_anyring(e.arg(0), RE, cmap);
        for (unsigned i = 1; i < e.num_args(); ++i)
        {
            poly pi = expr_to_poly_anyring(e.arg(i), RE, cmap);
            res = p_Mult_q(res, pi, R);
        }
        return res;
    }
    case Z3_OP_POWER:
    {
        if (e.num_args() != 2)
            throw std::runtime_error("expr_to_poly_anyring: POWER !=2");
        if (!(e.arg(1).is_numeral() && e.arg(1).get_sort().is_int()))
            throw std::runtime_error("expr_to_poly_anyring: POWER exponent must be Int numeral");

        mpz_t exz;
        mpz_init(exz);
        {
            Z3_string es = Z3_get_numeral_string((Z3_context)e.ctx(), (Z3_ast)e.arg(1));
            if (mpz_set_str(exz, es, 10) != 0)
            {
                mpz_clear(exz);
                throw std::runtime_error("expr_to_poly_anyring: bad exponent numeral");
            }
        }
        if (mpz_sgn(exz) < 0)
        {
            mpz_clear(exz);
            throw std::runtime_error("expr_to_poly_anyring: negative exponent");
        }
        if (!mpz_fits_ulong_p(exz))
        {
            mpz_clear(exz);
            throw std::runtime_error("expr_to_poly_anyring: exponent too large");
        }
        unsigned long ex = mpz_get_ui(exz);
        mpz_clear(exz);

        if (ex == 0)
            return poly_from_si(1, R);

        poly base = expr_to_poly_anyring(e.arg(0), RE, cmap);
        poly res = poly_from_si(1, R);
        while (ex > 0)
        {
            if (ex & 1)
            {
                poly new_res = poly_mul_clone(res, base, R);
                if (res)
                    p_Delete(&res, R);
                res = new_res;
            }
            ex >>= 1;
            if (ex)
            {
                poly new_base = poly_mul_clone(base, base, R);
                if (base)
                    p_Delete(&base, R);
                base = new_base;
            }
        }
        if (base)
            p_Delete(&base, R);
        return res;
    }
    default:
        throw std::runtime_error("expr_to_poly_anyring: unsupported op: " + e.decl().name().str());
    }
}

// ---------------- Poly(Int) term -> Singular poly ----------------
static int poly_num_terms(poly P)
{
    int n = 0;
    for (poly t = P; t != nullptr; t = pNext(t))
        ++n;
    return n;
}

static int poly_max_exp_in_var(poly P, const ring R, int var_idx_1based)
{
    int mx = 0;
    for (poly t = P; t != nullptr; t = pNext(t))
    {
        int e = p_GetExp(t, var_idx_1based, R);
        if (e > mx)
            mx = e;
    }
    return mx;
}

static poly polyterm_to_singular_poly(const expr &p,
                                      const IndetEnv &env,
                                      const std::vector<std::string> &indet_ring_names,
                                      RingEnv &RE,
                                      const CoeffVarMap &cmap,
                                      int Nc,
                                      const std::string &tag);

static poly polyterm_to_singular_poly(const expr &p,
                                      const IndetEnv &env,
                                      const std::vector<std::string> &indet_ring_names,
                                      RingEnv &RE,
                                      const CoeffVarMap &cmap,
                                      int Nc,
                                      const std::string &tag)
{
    ring R = RE.R;
    if (!R)
        throw std::runtime_error("polyterm_to_singular_poly: ring is null");
    rChangeCurrRing(R);

    if (is_ctor(p, "PConst", 1))
    {
        if (!p.arg(0).get_sort().is_int())
            throw std::runtime_error("PConst argument not Int: " + p.to_string());
        return expr_to_poly_anyring(p.arg(0), RE, cmap);
    }

    if (is_ctor(p, "PVar", 1))
    {
        std::string raw;
        if (!get_string_literal_smt(p.arg(0), raw))
            throw std::runtime_error("PVar expects a String literal: " + p.to_string());
        std::string id = raw;
        auto it = env.idx.find(id);
        if (it == env.idx.end())
            throw std::runtime_error("Unknown indet: " + id);
        std::string ringnm = indet_ring_names[it->second];
        int vi = RE.ensure_var_idx(ringnm);

        poly v = p_NSet(num_from_si(1, R->cf), R);
        p_SetExp(v, vi, 1, R);
        p_Setm(v, R);
        return v;
    }

    if (p.is_const() && !p.is_numeral() && is_poly_sort(p.get_sort()))
    {
        throw std::runtime_error(
            "Poly-sort constant is not allowed as an indeterminate: " + p.to_string() +
            " (use (PVar \"x\") or expand it into constructors like PAdd/PMul/PConst)");
    }

    if (is_ctor(p, "PNeg", 1))
    {
        poly a = polyterm_to_singular_poly(p.arg(0), env, indet_ring_names, RE, cmap, Nc, tag);
        number m1 = num_from_si(-1, R->cf);
        poly r = p_Mult_nn(a, m1, R);
        n_Delete(&m1, R->cf);
        return r;
    }
    if (is_ctor(p, "PAdd", 2))
    {
        poly a = polyterm_to_singular_poly(p.arg(0), env, indet_ring_names, RE, cmap, Nc, tag);
        poly b = polyterm_to_singular_poly(p.arg(1), env, indet_ring_names, RE, cmap, Nc, tag);
        return p_Add_q(a, b, R);
    }
    if (is_ctor(p, "PSub", 2))
    {
        poly a = polyterm_to_singular_poly(p.arg(0), env, indet_ring_names, RE, cmap, Nc, tag);
        poly b = polyterm_to_singular_poly(p.arg(1), env, indet_ring_names, RE, cmap, Nc, tag);
        number m1 = num_from_si(-1, R->cf);
        poly bn = p_Mult_nn(b, m1, R);
        n_Delete(&m1, R->cf);
        return p_Add_q(a, bn, R);
    }
    if (is_ctor(p, "PMul", 2))
    {
        poly a = polyterm_to_singular_poly(p.arg(0), env, indet_ring_names, RE, cmap, Nc, tag);
        poly b = polyterm_to_singular_poly(p.arg(1), env, indet_ring_names, RE, cmap, Nc, tag);
        return p_Mult_q(a, b, R);
    }
    if (is_ctor(p, "PPow", 2))
    {
        int64_t k = 0;
        if (!get_int64_numeral(p.arg(1), k) || k < 0)
            throw std::runtime_error("PPow exponent must be non-negative Int numeral: " + p.to_string());

        if (k == 0)
            return poly_from_si(1, R);

        if (k > MAX_POW_EXPAND)
        {
            std::cerr << "[fatal] PPow exponent too large: k=" << k
                      << " > MAX_POW_EXPAND=" << MAX_POW_EXPAND
                      << " (refuse to expand; abort)\n";
            std::exit(2);
        }

        const std::string base_s = PRINT_POW_BASE ? p.arg(0).to_string() : std::string();
        auto t0 = clk::now();

        poly base = polyterm_to_singular_poly(p.arg(0), env, indet_ring_names, RE, cmap, Nc, tag);

        if (k == 1)
        {
            auto t1 = clk::now();
            if (PRINT_POW_STATS)
            {
                int terms = poly_num_terms(base);
                int deg_u = -1;
                auto itu = env.idx.find("u");
                if (itu != env.idx.end())
                {
                    const std::string &u_ring = indet_ring_names[itu->second];
                    int uidx = RE.ensure_var_idx(u_ring);
                    deg_u = poly_max_exp_in_var(base, R, uidx);
                }
                auto us = std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0).count();
                double ms = us / 1000.0;

                std::cout << "[pow][" << tag << "] k=" << k
                          << " time=" << us << "us (" << ms << "ms)"
                          << " terms=" << terms
                          << " deg_u=" << ((deg_u >= 0) ? std::to_string(deg_u) : "NA");
                if (PRINT_POW_BASE)
                    std::cout << " base=" << base_s;
                std::cout << "\n";
            }
            return base;
        }

        poly res = poly_from_si(1, R);
        uint64_t e = (uint64_t)k;
        poly base_cur = base;

        while (e > 0)
        {
            if (e & 1)
            {
                poly new_res = poly_mul_clone(res, base_cur, R);
                if (res)
                    p_Delete(&res, R);
                res = new_res;
            }
            e >>= 1;
            if (e)
            {
                poly new_base = poly_mul_clone(base_cur, base_cur, R);
                if (base_cur)
                    p_Delete(&base_cur, R);
                base_cur = new_base;
            }
        }

        if (base_cur)
            p_Delete(&base_cur, R);

        auto t1 = clk::now();

        if (PRINT_POW_STATS)
        {
            int terms = poly_num_terms(res);
            int deg_u = -1;
            auto itu = env.idx.find("u");
            if (itu != env.idx.end())
            {
                const std::string &u_ring = indet_ring_names[itu->second];
                int uidx = RE.ensure_var_idx(u_ring);
                deg_u = poly_max_exp_in_var(res, R, uidx);
            }
            auto us = std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0).count();
            double ms = us / 1000.0;

            std::cout << "[pow][" << tag << "] k=" << k
                      << " time=" << us << "us (" << ms << "ms)"
                      << " terms=" << terms
                      << " deg_u=" << ((deg_u >= 0) ? std::to_string(deg_u) : "NA");
            if (PRINT_POW_BASE)
                std::cout << " base=" << base_s;
            std::cout << "\n";
        }

        return res;
    }

    throw std::runtime_error("Unsupported Poly term: " + p.to_string());
}

// ---------------- Ideal helpers ----------------
static ideal ideal_from_polys(const std::vector<poly> &gens, RingEnv &RE)
{
    ring R = RE.R;
    rChangeCurrRing(R);
    ideal I = idInit((int)gens.size(), 1);
    for (int i = 0; i < (int)gens.size(); ++i)
        I->m[i] = gens[i];
    return I;
}

static ideal groebner_std(ideal I, const ring R)
{
    rChangeCurrRing(R);
    ideal G = kStd(I, currRing->qideal, isNotHomog, NULL, NULL, 0, 0, NULL);
    return G;
}

static inline bool nf_is_zero(poly nf) { return nf == nullptr; }

static bool poly_equal(poly a, poly b, const ring R)
{
    rChangeCurrRing(R);

    if (a == nullptr && b == nullptr)
        return true;
    if (a == nullptr || b == nullptr)
        return false;

    poly ac = p_Copy(a, R);
    poly bc = p_Copy(b, R);

    number m1 = num_from_si(-1, R->cf);
    poly bneg = p_Mult_nn(bc, m1, R);
    n_Delete(&m1, R->cf);

    poly diff = p_Add_q(ac, bneg, R);
    bool eq = (diff == nullptr);

    if (diff)
        p_Delete(&diff, R);

    return eq;
}

// ---------------- Split D by indets ----------------
struct IndetKey
{
    std::vector<int> e;
    bool operator==(const IndetKey &o) const { return e == o.e; }
};

struct IndetKeyHash
{
    std::size_t operator()(const IndetKey &k) const noexcept
    {
        std::size_t h = 1469598103934665603ull;
        for (int x : k.e)
            h ^= (std::size_t)x + 0x9e3779b9 + (h << 6) + (h >> 2);
        return h;
    }
};

static std::unordered_map<IndetKey, poly, IndetKeyHash>
split_by_indets(poly D, int Nc, int Mi, RingEnv &RE)
{
    ring R = RE.R;
    rChangeCurrRing(R);

    std::unordered_map<IndetKey, poly, IndetKeyHash> out;

    for (poly t = D; t != nullptr; t = pNext(t))
    {
        IndetKey key;
        key.e.assign((size_t)Mi, 0);
        for (int j = 0; j < Mi; ++j)
        {
            int idx = Nc + 1 + j;
            key.e[(size_t)j] = p_GetExp(t, idx, R);
        }

        number a = p_GetCoeff(t, R);
        number ac = n_Copy(a, R->cf);

        poly ct = p_NSet(ac, R);
        for (int i = 0; i < Nc; ++i)
        {
            int idx = 1 + i;
            int e = p_GetExp(t, idx, R);
            if (e != 0)
                p_SetExp(ct, idx, e, R);
        }
        p_Setm(ct, R);

        auto it = out.find(key);
        if (it == out.end())
            out.emplace(std::move(key), ct);
        else
            it->second = p_Add_q(it->second, ct, R);
    }

    return out;
}

// ---------------- Singular coeff poly -> Z3 Int expr ----------------
static z3::expr z3_pow(z3::expr base, int exp)
{
    if (exp <= 0)
        return base.ctx().int_val(1);
    z3::expr res = base.ctx().int_val(1);
    z3::expr b = base;
    int e = exp;
    while (e > 0)
    {
        if (e & 1)
            res = res * b;
        e >>= 1;
        if (e)
            b = b * b;
    }
    return res;
}

static z3::expr coeff_poly_to_z3_expr(z3::context &c, poly P, const ring R, const CoeffVarMap &cmap, int Nc)
{
    if (P == nullptr)
        return c.int_val(0);

    z3::expr acc = c.int_val(0);

    for (poly t = P; t != nullptr; t = pNext(t))
    {
        number a = p_GetCoeff(t, R);
        std::string astr = number_to_decimal_string(a, R);
        z3::expr term = c.int_val(astr.c_str());

        for (int i = 0; i < Nc; ++i)
        {
            int idx = 1 + i;
            int e = p_GetExp(t, idx, R);
            if (e == 0)
                continue;
            term = term * z3_pow(cmap.z3_bases[(size_t)i], e);
        }
        acc = acc + term;
    }

    return acc.simplify();
}

// ---------------- eqP compilation ----------------
struct EqPCompiled
{
    expr atom;
    expr A;
    expr B;

    std::vector<expr> coeff_ints;
    std::vector<expr> coeff_eqs;
    expr coeff_neq_disj;
    bool always_equal = false;

    poly D_full = nullptr; // owned
};

static EqPCompiled compile_eqP_singular(const expr &atom, const expr &A, const expr &B,
                                        const std::string &label,
                                        const IndetEnv &env,
                                        const std::vector<std::string> &indet_ring_names,
                                        RingEnv &RE,
                                        const CoeffVarMap &cmap,
                                        int Nc, int Mi)
{
    context &zctx = atom.ctx();
    ring R = RE.R;
    rChangeCurrRing(R);

    EqPCompiled out{atom, A, B, {}, {}, zctx.bool_val(false), false, nullptr};

    poly pA = polyterm_to_singular_poly(A, env, indet_ring_names, RE, cmap, Nc, label + "/LHS");
    poly pB = polyterm_to_singular_poly(B, env, indet_ring_names, RE, cmap, Nc, label + "/RHS");

    LOG_INFO(g_log, "singular", label + " LHS(poly) = " + poly_to_string(pA, R));
    LOG_INFO(g_log, "singular", label + " RHS(poly) = " + poly_to_string(pB, R));

    number m1 = num_from_si(-1, R->cf);
    poly pBn = p_Mult_nn(pB, m1, R);
    n_Delete(&m1, R->cf);
    poly D = p_Add_q(pA, pBn, R);

    if (D == nullptr)
    {
        out.always_equal = true;
        out.coeff_neq_disj = zctx.bool_val(false);
        out.D_full = nullptr;
        return out;
    }

    out.D_full = p_Copy(D, R);

    auto groups = split_by_indets(D, Nc, Mi, RE);
    if (D)
        p_Delete(&D, R);

    expr disj = zctx.bool_val(false);

    for (auto &kv : groups)
    {
        poly coeffP = kv.second;

        expr coeffE = coeff_poly_to_z3_expr(zctx, coeffP, R, cmap, Nc);
        out.coeff_ints.push_back(coeffE);

        expr eq0 = (coeffE == zctx.int_val(0)).simplify();
        if (!eq0.is_true())
            out.coeff_eqs.push_back(eq0);

        expr ne0 = (coeffE != zctx.int_val(0)).simplify();
        if (ne0.is_true())
            disj = zctx.bool_val(true);
        else if (!ne0.is_false() && !disj.is_true())
            disj = (disj || ne0).simplify();

        if (coeffP)
            p_Delete(&coeffP, R);
    }

    out.coeff_neq_disj = disj.simplify();
    return out;
}

// ---------------- eqmodP1 compilation ----------------
struct EqModPCompiled
{
    expr atom;
    expr A;
    expr B;
    expr Mterm;

    bool modulus_ok = false;
    bool modulus_is_const = false;
    mpz_class m_const = 0;

    poly M_poly = nullptr; // owned
    poly D = nullptr;      // owned: D = A - B

    std::string u_name;      // fresh quotient variable in ring
    poly U_poly = nullptr;   // owned: monomial u_t
    poly true_gen = nullptr; // owned: D - U_poly * M_poly
};

static bool extract_modulus_from_polyconst(const expr &Mterm, mpz_class &m_out)
{
    if (!is_ctor(Mterm, "PConst", 1))
        return false;
    expr m = Mterm.arg(0);
    if (!(m.is_numeral() && m.get_sort().is_int()))
        return false;

    Z3_string ms = Z3_get_numeral_string((Z3_context)m.ctx(), (Z3_ast)m);
    mpz_class mv;
    if (mv.set_str(ms, 10) != 0)
        return false;
    if (mv <= 0)
        return false;

    m_out = mv;
    return true;
}

static poly make_var_poly(RingEnv &RE, const std::string &name)
{
    ring R = RE.R;
    rChangeCurrRing(R);
    int vi = RE.ensure_var_idx(name);

    poly p = p_NSet(num_from_si(1, R->cf), R);
    p_SetExp(p, vi, 1, R);
    p_Setm(p, R);
    return p;
}

static EqModPCompiled compile_eqmodP1_singular(const expr &atom, const expr &A, const expr &B, const expr &Mterm,
                                               const std::string &label,
                                               const IndetEnv &env,
                                               const std::vector<std::string> &indet_ring_names,
                                               RingEnv &RE,
                                               const CoeffVarMap &cmap,
                                               int Nc,
                                               const std::string &u_name)
{
    ring R = RE.R;
    rChangeCurrRing(R);

    EqModPCompiled out{
        atom,
        A,
        B,
        Mterm,
        false,
        false,
        0,
        nullptr,
        nullptr,
        u_name,
        nullptr,
        nullptr};

    poly pA = polyterm_to_singular_poly(A, env, indet_ring_names, RE, cmap, Nc, label + "/LHS");
    poly pB = polyterm_to_singular_poly(B, env, indet_ring_names, RE, cmap, Nc, label + "/RHS");

    number m1 = num_from_si(-1, R->cf);
    poly pBn = p_Mult_nn(pB, m1, R);
    n_Delete(&m1, R->cf);
    out.D = p_Add_q(pA, pBn, R);

    mpz_class mv;
    if (extract_modulus_from_polyconst(Mterm, mv))
    {
        out.modulus_ok = true;
        out.modulus_is_const = true;
        out.m_const = mv;
        out.M_poly = poly_from_mpz(mv, R);
    }
    else
    {
        out.M_poly = polyterm_to_singular_poly(Mterm, env, indet_ring_names, RE, cmap, Nc, label + "/MOD");
        out.modulus_ok = (out.M_poly != nullptr);
    }

    if (out.modulus_ok)
    {
        out.U_poly = make_var_poly(RE, u_name);
        poly um = poly_mul_clone(out.U_poly, out.M_poly, R);

        number neg1 = num_from_si(-1, R->cf);
        poly um_neg = p_Mult_nn(um, neg1, R);
        n_Delete(&neg1, R->cf);

        out.true_gen = p_Add_q(p_Copy(out.D, R), um_neg, R);
    }

    LOG_INFO(g_log, "singular", label + " D(poly) = " + poly_to_string(out.D, R));
    if (out.M_poly)
        LOG_INFO(g_log, "singular", label + " M(poly) = " + poly_to_string(out.M_poly, R));
    if (out.true_gen)
        LOG_INFO(g_log, "singular", label + " true_gen(poly) = " + poly_to_string(out.true_gen, R));

    return out;
}

// -------------------------- Propagator --------------------------
class PolyPropagator : public user_propagator_base
{
    IndetEnv m_env;
    CoeffVarMap m_cmap;

    std::vector<std::string> m_indet_ring_names;
    std::vector<std::string> m_ring_vars;
    std::vector<std::string> m_qvar_names;

    int m_Nc = 0;
    int m_Mi = 0;

    std::vector<EqPCompiled> m_eqp;
    std::vector<EqModPCompiled> m_eqmodp;

    std::unordered_map<Z3_ast, Z3_lbool> m_bool_cache;

    RingEnv m_RE;

    std::unordered_map<Z3_ast, std::string> m_label;

    std::string label_of(const expr &e) const
    {
        auto it = m_label.find((Z3_ast)e);
        if (it != m_label.end())
            return it->second;
        return e.to_string();
    }

    void log_fixed(const expr &t, const expr &v)
    {
        if (!PRINT_FIXED_ALL)
            return;
        if (t.is_numeral())
            return;
        if (t.is_bool() && (t.is_true() || t.is_false()))
            return;

        LOG_TRACE(g_log, "fixed", label_of(t) + " = " + v.to_string());
    }

    void log_propagate(const expr &from, const expr &infer)
    {
        if (!PRINT_PROPAGATE)
            return;

        LOG_TRACE(g_log, "propagate", label_of(from) + " ==> " + infer.to_string());
    }

    Z3_lbool lbool_of(const expr &a) const
    {
        auto it = m_bool_cache.find((Z3_ast)a);
        if (it == m_bool_cache.end())
            return Z3_L_UNDEF;
        return it->second;
    }

    void add_and_propagate_all(const expr &ante, const std::vector<expr> &cons)
    {
        expr_vector ants(ctx());
        ants.push_back(ante);
        for (auto &cns : cons)
        {
            this->add(cns);
            log_propagate(ante, cns);
            this->propagate(ants, cns);
        }
    }

    void add_and_propagate_one(const expr &ante, const expr &conseq)
    {
        expr_vector ants(ctx());
        ants.push_back(ante);
        this->add(conseq);
        log_propagate(ante, conseq);
        this->propagate(ants, conseq);
    }

    void conflict_with(const std::vector<expr> &ants_vec)
    {
        expr_vector ants(ctx());
        for (auto &a : ants_vec)
            ants.push_back(a);
        this->conflict(ants);
    }

    bool same_modulus_across_eqmodp() const
    {
        if (m_eqmodp.empty())
            return true;

        ring R = m_RE.R;
        if (R == nullptr)
            return false;
        rChangeCurrRing(R);

        const auto &c0 = m_eqmodp[0];
        if (!c0.modulus_ok || c0.M_poly == nullptr)
        {
            LOG_INFO(g_log, "singular",
                     "same_modulus_across_eqmodp: eqmodP1#0 has invalid modulus");
            return false;
        }

        LOG_INFO(g_log, "singular",
                 "Reference modulus eqmodP1#0 M(poly) = " + poly_to_string(c0.M_poly, R));

        for (size_t i = 1; i < m_eqmodp.size(); ++i)
        {
            const auto &ci = m_eqmodp[i];

            if (!ci.modulus_ok || ci.M_poly == nullptr)
            {
                LOG_INFO(g_log, "singular",
                         "same_modulus_across_eqmodp: eqmodP1#" + std::to_string(i) +
                             " has invalid modulus");
                return false;
            }

            bool same = poly_equal(ci.M_poly, c0.M_poly, R);

            LOG_INFO(g_log, "singular",
                     "Compare modulus eqmodP1#" + std::to_string(i) +
                         " against eqmodP1#0 : " + std::string(same ? "SAME" : "DIFF"));

            if (!same)
            {
                LOG_INFO(g_log, "singular",
                         "  eqmodP1#0 M(poly) = " + poly_to_string(c0.M_poly, R));
                LOG_INFO(g_log, "singular",
                         "  eqmodP1#" + std::to_string(i) +
                             " M(poly) = " + poly_to_string(ci.M_poly, R));
                return false;
            }
        }

        return true;
    }
    std::vector<poly> collect_true_context_generators(std::vector<expr> &ants_out)
    {
        ring R = m_RE.R;
        rChangeCurrRing(R);

        std::vector<poly> gens;
        ants_out.clear();

        if (m_eqmodp.empty())
            return gens;
        if (!same_modulus_across_eqmodp())
            return gens;

        gens.push_back(p_Copy(m_eqmodp[0].M_poly, R));

        for (auto &ep : m_eqp)
        {
            if (ep.D_full == nullptr)
                continue;
            if (lbool_of(ep.atom) != Z3_L_TRUE)
                continue;

            gens.push_back(p_Copy(ep.D_full, R));
            ants_out.push_back(ep.atom);
        }

        for (auto &cp : m_eqmodp)
        {
            if (lbool_of(cp.atom) != Z3_L_TRUE)
                continue;
            if (cp.true_gen == nullptr)
                continue;

            gens.push_back(p_Copy(cp.true_gen, R));
            ants_out.push_back(cp.atom);
        }

        return gens;
    }

    void on_fixed_eqP(const expr &atom, Z3_lbool bv)
    {
        for (auto &cp : m_eqp)
        {
            if (!z3::eq(atom, cp.atom))
                continue;

            if (bv == Z3_L_TRUE)
            {
                if (!cp.always_equal)
                {
                    for (auto &eq0 : cp.coeff_eqs)
                    {
                        if (eq0.is_false())
                        {
                            conflict_with({atom});
                            return;
                        }
                    }
                    add_and_propagate_all(atom, cp.coeff_eqs);
                }
                return;
            }

            if (bv == Z3_L_FALSE)
            {
                if (cp.coeff_neq_disj.is_false())
                {
                    conflict_with({atom});
                    return;
                }
                add_and_propagate_one(atom, cp.coeff_neq_disj);
                return;
            }
        }
    }

    // ---------------- eqmodP1: all-false ----------------
    void check_eqmodP1_all_false_refutation()
    {
        if (!ENABLE_ALL_FALSE)
            return;
        if (m_eqmodp.empty())
            return;

        for (auto &cp : m_eqmodp)
        {
            Z3_lbool bv = lbool_of(cp.atom);
            if (bv == Z3_L_UNDEF)
                return;
            if (bv != Z3_L_FALSE)
                return;
            if (!cp.modulus_ok)
                return;
        }

        if (!same_modulus_across_eqmodp())
            return;

        ring R = m_RE.R;
        rChangeCurrRing(R);

        LOG_INFO(g_log, "singular", "=== eqmodP1(all-false) refutation begin ===");

        std::vector<expr> true_eqp_atoms;
        std::vector<poly> gens;
        gens.reserve(1 + m_eqp.size());

        gens.push_back(p_Copy(m_eqmodp[0].M_poly, R));

        for (auto &ep : m_eqp)
        {
            if (ep.D_full == nullptr)
                continue;
            if (lbool_of(ep.atom) != Z3_L_TRUE)
                continue;

            gens.push_back(p_Copy(ep.D_full, R));
            true_eqp_atoms.push_back(ep.atom);
        }

        LOG_INFO(g_log, "singular", "Using " + std::to_string((int)true_eqp_atoms.size()) + " TRUE eqP equation(s) in ideal.");

        ideal I = ideal_from_polys(gens, m_RE);
        print_ideal("I", I, R);

        LOG_INFO(g_log, "singular", "Computing Groebner basis G = std(I) ...");
        LOG_DEBUG(g_log, "kStd", "---------------start---------------");
        ideal G = groebner_std(I, R);
        LOG_DEBUG(g_log, "kStd", "---------------end---------------");

        print_ideal("G", G, R);

        bool hit = false;
        expr hit_atom = ctx().bool_val(false);

        for (auto &cp : m_eqmodp)
        {
            poly d = p_Copy(cp.D, R);

            LOG_DEBUG(g_log, "knf", "---------------start---------------");
            poly nf = kNF(G, currRing->qideal, d, 0, 0);
            LOG_DEBUG(g_log, "knf", "---------------end---------------");

            bool in = nf_is_zero(nf);

            LOG_INFO(g_log, "singular",
                     "Query instance: " + label_of(cp.atom) +
                         " ; D=" + poly_to_string(cp.D, R) +
                         " ; NF_G(D)=" + poly_to_string(nf, R) +
                         " ; D ∈ <M, {TRUE eqP}>? " + std::string(in ? "YES" : "NO"));

            if (nf)
                p_Delete(&nf, R);
            if (d)
                p_Delete(&d, R);

            if (in)
            {
                LOG_INFO(g_log, "singular",
                         "[eqmodP1] all-false refute: " + label_of(cp.atom) +
                             " has D in <M, {TRUE eqP}>; cannot be FALSE");
                hit = true;
                hit_atom = cp.atom;
                break;
            }
        }

        if (hit)
        {
            std::vector<expr> ants;
            ants.reserve(m_eqmodp.size() + true_eqp_atoms.size());

            for (auto &cp : m_eqmodp)
                ants.push_back(cp.atom);
            for (auto &a : true_eqp_atoms)
                ants.push_back(a);

            if (!hit_atom.is_false())
                ants.push_back(hit_atom);

            conflict_with(ants);
        }

        if (G)
            idDelete(&G);
        if (I)
            idDelete(&I);

        LOG_INFO(g_log, "singular", "=== eqmodP1(all-false) refutation end ===");
    }

    // ---------------- eqmodP1: all-true ----------------
    void check_eqmodP1_all_true_refutation()
    {
        if (!ENABLE_ALL_TRUE)
            return;
        if (m_eqmodp.empty())
            return;

        for (auto &cp : m_eqmodp)
        {
            Z3_lbool bv = lbool_of(cp.atom);
            if (bv == Z3_L_UNDEF)
                return;
            if (bv != Z3_L_TRUE)
                return;
            if (!cp.modulus_ok)
                return;
        }

        if (!same_modulus_across_eqmodp())
            return;

        ring R = m_RE.R;
        rChangeCurrRing(R);

        LOG_INFO(g_log, "singular", "=== eqmodP1(all-true) refutation begin ===");

        std::vector<expr> ants;
        std::vector<poly> gens = collect_true_context_generators(ants);
        if (gens.empty())
            return;

        ideal J = ideal_from_polys(gens, m_RE);
        print_ideal("J_all_true", J, R);

        LOG_INFO(g_log, "singular", "Computing Groebner basis G = std(J) ...");
        LOG_DEBUG(g_log, "kStd", "---------------start---------------");
        ideal G = groebner_std(J, R);
        LOG_DEBUG(g_log, "kStd", "---------------end---------------");

        print_ideal("G_all_true", G, R);

        poly one = poly_from_si(1, R);

        LOG_DEBUG(g_log, "knf", "---------------start---------------");
        poly nf = kNF(G, currRing->qideal, one, 0, 0);
        LOG_DEBUG(g_log, "knf", "---------------end---------------");

        bool unsat = nf_is_zero(nf);

        LOG_INFO(g_log, "singular",
                 "ALL-TRUE check: NF_G(1)=" + poly_to_string(nf, R) +
                     " ; 1 ∈ J ? " + std::string(unsat ? "YES" : "NO"));

        if (nf)
            p_Delete(&nf, R);
        if (G)
            idDelete(&G);
        if (J)
            idDelete(&J);

        if (unsat)
        {
            LOG_INFO(g_log, "singular", "[eqmodP1] all-true refute: 1 ∈ J");
            conflict_with(ants);
        }

        LOG_INFO(g_log, "singular", "=== eqmodP1(all-true) refutation end ===");
    }

    // ---------------- eqmodP1: mixed ----------------
    void check_eqmodP1_mixed_refutation()
    {
        if (!ENABLE_MIXED)
            return;
        if (m_eqmodp.empty())
            return;

        bool has_true = false;
        bool has_false = false;

        for (auto &cp : m_eqmodp)
        {
            Z3_lbool bv = lbool_of(cp.atom);
            if (bv == Z3_L_UNDEF)
                return;
            if (!cp.modulus_ok)
                return;

            if (bv == Z3_L_TRUE)
                has_true = true;
            else if (bv == Z3_L_FALSE)
                has_false = true;
        }

        if (!(has_true && has_false))
            return;

        if (!same_modulus_across_eqmodp())
            return;

        ring R = m_RE.R;
        rChangeCurrRing(R);

        LOG_INFO(g_log, "singular", "=== eqmodP1(mixed) refutation begin ===");

        std::vector<expr> true_context_ants;
        std::vector<poly> gens = collect_true_context_generators(true_context_ants);
        if (gens.empty())
            return;

        ideal J = ideal_from_polys(gens, m_RE);
        print_ideal("J_mixed", J, R);

        LOG_INFO(g_log, "singular", "Computing Groebner basis G = std(J) ...");
        LOG_DEBUG(g_log, "kStd", "---------------start---------------");
        ideal G = groebner_std(J, R);
        LOG_DEBUG(g_log, "kStd", "---------------end---------------");

        print_ideal("G_mixed", G, R);

        bool hit = false;
        expr hit_atom = ctx().bool_val(false);

        for (auto &cp : m_eqmodp)
        {
            if (lbool_of(cp.atom) != Z3_L_FALSE)
                continue;

            poly d = p_Copy(cp.D, R);

            LOG_DEBUG(g_log, "knf", "---------------start---------------");
            poly nf = kNF(G, currRing->qideal, d, 0, 0);
            LOG_DEBUG(g_log, "knf", "---------------end---------------");

            bool in = nf_is_zero(nf);

            LOG_INFO(g_log, "singular",
                     "MIXED query instance: " + label_of(cp.atom) +
                         " ; D=" + poly_to_string(cp.D, R) +
                         " ; NF_G(D)=" + poly_to_string(nf, R) +
                         " ; D ∈ J ? " + std::string(in ? "YES" : "NO"));

            if (nf)
                p_Delete(&nf, R);
            if (d)
                p_Delete(&d, R);

            if (in)
            {
                LOG_INFO(g_log, "singular",
                         "[eqmodP1] mixed refute: " + label_of(cp.atom) +
                             " has D in J; cannot be FALSE");
                hit = true;
                hit_atom = cp.atom;
                break;
            }
        }

        if (G)
            idDelete(&G);
        if (J)
            idDelete(&J);

        if (hit)
        {
            std::vector<expr> ants = true_context_ants;
            ants.push_back(hit_atom);
            conflict_with(ants);
        }

        LOG_INFO(g_log, "singular", "=== eqmodP1(mixed) refutation end ===");
    }

    void check_eqmodP1_conflicts()
    {
        check_eqmodP1_all_false_refutation();
        check_eqmodP1_all_true_refutation();
        check_eqmodP1_mixed_refutation();
    }

public:
    PolyPropagator(solver *s,
                   const std::vector<expr> &eqps,
                   const std::vector<expr> &lhs,
                   const std::vector<expr> &rhs,
                   const std::vector<expr> &eqmodsP1,
                   const IndetEnv &env,
                   const CoeffVarMap &cmap,
                   const std::vector<std::string> &indet_ring_names,
                   const std::vector<std::string> &ring_vars,
                   const std::vector<std::string> &qvar_names)
        : user_propagator_base(s), m_env(env), m_cmap(cmap),
          m_indet_ring_names(indet_ring_names), m_ring_vars(ring_vars), m_qvar_names(qvar_names)
    {
        init_singular();

        register_fixed();
        register_final();
        register_created();

        m_Nc = (int)m_cmap.z3_bases.size();
        m_Mi = (int)m_env.names.size();

        coeffs cfZ = nInitChar(n_Z, nullptr);
        if (!cfZ)
            throw std::runtime_error("n_Z unavailable for Singular.");

        m_RE.build(cfZ, m_ring_vars, ringorder_lp);

        for (size_t i = 0; i < eqps.size(); ++i)
        {
            this->add(eqps[i]);
            this->add(lhs[i]);
            this->add(rhs[i]);

            std::string label = "eqP#" + std::to_string(i);
            m_label[(Z3_ast)eqps[i]] = label;

            EqPCompiled cp = compile_eqP_singular(eqps[i], lhs[i], rhs[i],
                                                  label,
                                                  m_env, m_indet_ring_names, m_RE, m_cmap,
                                                  m_Nc, m_Mi);

            for (auto &e : cp.coeff_eqs)
                this->add(e);
            this->add(cp.coeff_neq_disj);
            for (auto &ci : cp.coeff_ints)
                this->add(ci);

            m_eqp.push_back(std::move(cp));
        }

        if (m_qvar_names.size() < eqmodsP1.size())
            throw std::runtime_error("qvar_names size is smaller than eqmodsP1 size");

        for (size_t i = 0; i < eqmodsP1.size(); ++i)
        {
            auto &em = eqmodsP1[i];
            this->add(em);
            for (unsigned j = 0; j < 3; ++j)
                this->add(em.arg(j));

            std::string label = "eqmodP1#" + std::to_string(i);
            m_label[(Z3_ast)em] = label;

            EqModPCompiled cp = compile_eqmodP1_singular(em, em.arg(0), em.arg(1), em.arg(2),
                                                         label,
                                                         m_env, m_indet_ring_names, m_RE, m_cmap,
                                                         m_Nc,
                                                         m_qvar_names[i]);
            m_eqmodp.push_back(std::move(cp));
        }
    }

    PolyPropagator(context &c,
                   const IndetEnv &env,
                   const CoeffVarMap &cmap,
                   const std::vector<std::string> &indet_ring_names,
                   const std::vector<std::string> &ring_vars,
                   const std::vector<std::string> &qvar_names)
        : user_propagator_base(c), m_env(env), m_cmap(cmap),
          m_indet_ring_names(indet_ring_names), m_ring_vars(ring_vars), m_qvar_names(qvar_names)
    {
        init_singular();
        register_fixed();
        register_final();
        register_created();

        m_Nc = (int)m_cmap.z3_bases.size();
        m_Mi = (int)m_env.names.size();

        coeffs cfZ = nInitChar(n_Z, nullptr);
        if (!cfZ)
            throw std::runtime_error("n_Z unavailable for Singular.");

        m_RE.build(cfZ, m_ring_vars, ringorder_lp);
    }

    ~PolyPropagator() override
    {
        ring R = m_RE.R;
        if (R)
        {
            rChangeCurrRing(R);

            for (auto &cp : m_eqmodp)
            {
                if (cp.D)
                    p_Delete(&cp.D, R);
                cp.D = nullptr;

                if (cp.M_poly)
                    p_Delete(&cp.M_poly, R);
                cp.M_poly = nullptr;

                if (cp.U_poly)
                    p_Delete(&cp.U_poly, R);
                cp.U_poly = nullptr;

                if (cp.true_gen)
                    p_Delete(&cp.true_gen, R);
                cp.true_gen = nullptr;
            }

            for (auto &ep : m_eqp)
            {
                if (ep.D_full)
                    p_Delete(&ep.D_full, R);
                ep.D_full = nullptr;
            }
        }
    }

    void push() override {}
    void pop(unsigned) override {}
    void eq(const expr &, const expr &) override {}

    void created(const expr &t) override
    {
        if (!t.is_app())
            return;

        if (t.decl().name().str() == "eqP" && t.num_args() == 2)
        {
            expr A = t.arg(0), B = t.arg(1);
            this->add(t);
            this->add(A);
            this->add(B);

            std::string label = "eqP#" + std::to_string((int)m_eqp.size());
            m_label[(Z3_ast)t] = label;

            EqPCompiled cp = compile_eqP_singular(t, A, B,
                                                  label,
                                                  m_env, m_indet_ring_names, m_RE, m_cmap,
                                                  m_Nc, m_Mi);

            for (auto &e : cp.coeff_eqs)
                this->add(e);
            this->add(cp.coeff_neq_disj);
            for (auto &ci : cp.coeff_ints)
                this->add(ci);

            m_eqp.push_back(std::move(cp));

            check_eqmodP1_conflicts();
            return;
        }

        if (t.decl().name().str() == "eqmodP1" && t.num_args() == 3)
        {
            expr A = t.arg(0), B = t.arg(1), M = t.arg(2);
            this->add(t);
            this->add(A);
            this->add(B);
            this->add(M);

            size_t idx = m_eqmodp.size();
            if (idx >= m_qvar_names.size())
                throw std::runtime_error("created(eqmodP1): no preallocated qvar name; ensure all eqmodP1 are present in input SMT2");

            std::string label = "eqmodP1#" + std::to_string((int)idx);
            m_label[(Z3_ast)t] = label;

            EqModPCompiled cp = compile_eqmodP1_singular(t, A, B, M,
                                                         label,
                                                         m_env, m_indet_ring_names, m_RE, m_cmap,
                                                         m_Nc,
                                                         m_qvar_names[idx]);
            m_eqmodp.push_back(std::move(cp));

            check_eqmodP1_conflicts();
            return;
        }
    }

    void fixed(const expr &t, const expr &v) override
    {
        log_fixed(t, v);

        if (t.is_numeral())
            return;

        if (t.is_bool())
        {
            Z3_lbool bv = Z3_get_bool_value(ctx(), (Z3_ast)v);
            m_bool_cache[(Z3_ast)t] = bv;

            if (t.is_app() && t.decl().name().str() == "eqP" && t.num_args() == 2)
            {
                on_fixed_eqP(t, bv);
                check_eqmodP1_conflicts();
            }

            if (t.is_app() && t.decl().name().str() == "eqmodP1" && t.num_args() == 3)
            {
                check_eqmodP1_conflicts();
            }
        }
    }

    void final() override
    {
        check_eqmodP1_conflicts();
        std::cout << "===== [final] =====\n";
    }

    user_propagator_base *fresh(context &nctx) override
    {
        return new PolyPropagator(nctx, m_env, m_cmap, m_indet_ring_names, m_ring_vars, m_qvar_names);
    }
};

// ---------------- main ----------------
static int coeff_priority_rank(const std::string &pretty)
{
    static const std::vector<std::string> pr = {
        "r_final_1",
        "r_sum_2",
        "r_sum_1",
        "r_diff_2",
        "r_diff_1",
        "r_m_1",
        "a_0",
        "b_0",
        "c_1",
    };
    for (int i = 0; i < (int)pr.size(); ++i)
        if (pretty == pr[i])
            return i;
    return 1000000;
}

int main(int argc, char **argv)
{
    g_log.enable_file("run.log");

    try
    {
        if (argc < 2)
        {
            std::cerr << "Usage: " << argv[0]
                      << " <input.smt2> [--quiet] [--ring-detail] [--no-pow-stats] [--no-pow-base]"
                         " [--expr-len=N] [--disable-all-false] [--disable-all-true] [--disable-mixed]\n";
            return 1;
        }

        for (int i = 2; i < argc; ++i)
        {
            std::string a = argv[i];
            if (a == "--quiet")
                SINGULAR_VERBOSE = false;
            if (a == "--ring-detail")
                PRINT_RING_DETAIL = true;
            if (a == "--no-pow-stats")
                PRINT_POW_STATS = false;
            if (a == "--no-pow-base")
                PRINT_POW_BASE = false;
            if (a == "--order")
                ORDER = false;
            if (a == "--env")
                ENV = true;
            if (a == "--skipal")
                SKIP_ALL_TRUE = true;
            if (a == "--no-trace")
                g_log.set_global(LogLevel::Debug);

            if (a == "--disable-all-false")
                ENABLE_ALL_FALSE = false;
            if (a == "--disable-all-true")
                ENABLE_ALL_TRUE = false;
            if (a == "--disable-mixed")
                ENABLE_MIXED = false;

            if (a.rfind("--expr-len=", 0) == 0)
                LOG_EXPR_MAXLEN = std::stoul(a.substr(std::string("--expr-len=").size()));
        }

        LOG_TRACE(g_log, "parse", "Reading SMT2 file: " + std::string(argv[1]));

        context c;

        std::string raw = read_file_all(argv[1]);
        std::string smt = inject_poly_eqP_eqmodP_if_missing(raw);

        std::vector<expr> asserts = parse_smt2_assertions(c, smt);

        LOG_TRACE(g_log, "parse", "Loaded " + std::to_string(asserts.size()) + " assertions.");

        solver s(c);

        for (size_t i = 0; i < asserts.size(); ++i)
        {
            std::string nm = "A#" + std::to_string(i);
            expr tag = c.bool_const(nm.c_str());

            Z3_solver_assert_and_track(
                (Z3_context)c,
                (Z3_solver)s,
                (Z3_ast)asserts[i],
                (Z3_ast)tag);
        }

        std::vector<expr> eqps;
        for (auto &f : asserts)
            collect_eqP_rec(f, eqps);

        std::vector<expr> lhs, rhs;
        lhs.reserve(eqps.size());
        rhs.reserve(eqps.size());
        for (size_t i = 0; i < eqps.size(); ++i)
        {
            LOG_TRACE(g_log, "parse", "Found eqP#" + std::to_string(i) + " constraint: " + eqps[i].to_string());
            lhs.push_back(eqps[i].arg(0));
            rhs.push_back(eqps[i].arg(1));
        }

        std::vector<expr> eqmodsP1;
        for (auto &f : asserts)
            collect_eqmodP1_rec(f, eqmodsP1);

        for (size_t i = 0; i < eqmodsP1.size(); ++i)
        {
            LOG_TRACE(g_log, "parse",
                      "Found eqmodP1#" + std::to_string(i) +
                          " constraint: " + eqmodsP1[i].to_string());
        }

        std::vector<std::string> indets = collect_all_indets(asserts);
        IndetEnv env;
        env.names = indets;
        for (unsigned i = 0; i < env.names.size(); ++i)
            env.idx[env.names[i]] = i;

        std::unordered_set<Z3_ast> baseS;
        for (auto &f : asserts)
            collect_coeff_bases_rec(f, baseS);

        std::vector<z3::expr> bases;
        bases.reserve(baseS.size());
        for (auto a : baseS)
            bases.emplace_back(c, a);

        if (ORDER)
        {
            std::stable_sort(bases.begin(), bases.end(),
                             [](const z3::expr &x, const z3::expr &y)
                             {
                                 std::string nx = coeff_base_pretty_name(x);
                                 std::string ny = coeff_base_pretty_name(y);
                                 int rx = coeff_priority_rank(nx);
                                 int ry = coeff_priority_rank(ny);
                                 if (rx != ry)
                                     return rx < ry;
                                 return x.to_string() < y.to_string();
                             });
        }
        else
        {
            std::sort(bases.begin(), bases.end(),
                      [](const z3::expr &x, const z3::expr &y)
                      { return x.to_string() < y.to_string(); });
        }

        std::unordered_set<std::string> used;

        CoeffVarMap cmap;
        cmap.z3_bases = bases;
        cmap.ring_names.resize(bases.size());

        for (size_t i = 0; i < bases.size(); ++i)
        {
            std::string base_name = coeff_base_pretty_name(bases[i]);
            std::string base = sanitize_ring_var_base(base_name);
            cmap.ring_names[i] = make_unique_name(base, used);
        }

        cmap.base_to_index.clear();
        for (size_t i = 0; i < bases.size(); ++i)
            cmap.base_to_index[(Z3_ast)bases[i]] = (unsigned)i;

        std::vector<std::string> indet_ring_names(env.names.size());
        for (size_t i = 0; i < env.names.size(); ++i)
        {
            std::string base = sanitize_ring_var_base(env.names[i]);
            indet_ring_names[i] = make_unique_name(base, used);
        }

        std::vector<std::string> qvar_names(eqmodsP1.size());
        for (size_t i = 0; i < eqmodsP1.size(); ++i)
        {
            qvar_names[i] = make_unique_name("u_mod_" + std::to_string(i), used);
        }

        std::vector<std::string> ring_vars;
        ring_vars.reserve(cmap.ring_names.size() + indet_ring_names.size() + qvar_names.size());
        ring_vars.insert(ring_vars.end(), cmap.ring_names.begin(), cmap.ring_names.end());
        ring_vars.insert(ring_vars.end(), indet_ring_names.begin(), indet_ring_names.end());
        ring_vars.insert(ring_vars.end(), qvar_names.begin(), qvar_names.end());

        LOG_TRACE(g_log, "init",
                  "Initializing propagator with " +
                      std::to_string(eqps.size()) + " eqP constraint(s), " +
                      std::to_string(eqmodsP1.size()) + " eqmodP1 constraint(s).");

        PolyPropagator up(&s, eqps, lhs, rhs, eqmodsP1,
                          env, cmap, indet_ring_names, ring_vars, qvar_names);

        auto t0 = clk::now();
        check_result r = s.check();
        auto t1 = clk::now();

        std::cout << "Solver result: " << r << "\n";
        if (SHOW_MODEL && r == sat)
            std::cout << "Model:\n"
                      << s.get_model() << "\n";

        std::cout << "[timer] z3.check() = " << fmt_duration(t1 - t0) << "\n";

        return 0;
    }
    catch (const z3::exception &ex)
    {
        std::cerr << "Z3 error: " << ex.msg() << "\n";
        return 1;
    }
    catch (const std::exception &ex)
    {
        std::cerr << "Error: " << ex.what() << "\n";
        return 1;
    }
}