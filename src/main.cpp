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
#include <iterator>
#include <map>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include <sstream>
#include <functional>

#include "util/fmt_duration.hpp"
#include "util/logger.hpp"
#include "util/rewrite.hpp"

using namespace z3;
using clk = std::chrono::steady_clock;

static bool SHOW_MODEL = true;
static bool PRINT_RING_DETAIL = false;
static bool PRINT_FIXED_ALL = true;
static bool PRINT_PROPAGATE = true;
static constexpr int64_t MAX_POW_EXPAND = 65536;
static util::Logger g_log;

class TeeStreamBuf : public std::streambuf
{
    std::streambuf *a_;
    std::streambuf *b_;

public:
    TeeStreamBuf(std::streambuf *a, std::streambuf *b) : a_(a), b_(b) {}

protected:
    int overflow(int ch) override
    {
        if (ch == EOF)
            return !EOF;
        const int ra = a_ ? a_->sputc((char)ch) : ch;
        const int rb = b_ ? b_->sputc((char)ch) : ch;
        return (ra == EOF || rb == EOF) ? EOF : ch;
    }

    int sync() override
    {
        const int sa = a_ ? a_->pubsync() : 0;
        const int sb = b_ ? b_->pubsync() : 0;
        return (sa == 0 && sb == 0) ? 0 : -1;
    }
};

class ScopedStreamBuf
{
    std::ostream &stream_;
    std::streambuf *old_;

public:
    ScopedStreamBuf(std::ostream &stream, std::streambuf *next)
        : stream_(stream), old_(stream.rdbuf(next)) {}

    ~ScopedStreamBuf()
    {
        stream_.rdbuf(old_);
    }
};

static bool ENV = false;
static bool ENABLE_ALL_FALSE = true;
static bool ENABLE_ALL_TRUE = true;
static bool ENABLE_MIXED = true;
static bool ALL_FALSE_ASSUME_M_PRIME = false;
static bool ENABLE_REWRITING = true;
// The OCaml-style rewriter extracts variable assignments by default. Optional
// safety/coverage knobs remain exposed:
//   * PRESERVE_EQMODP1_VARS (default false): opt back into the older
//     conservative mode that never extracts a rule whose LHS appears in any
//     eqmodP1 atom.
//   * ENABLE_SUBEXPRESSION_RULES (default false): opt into separable
//     sub-expression assignment extraction.
//   * ENABLE_EXPRESSION_GROWTH_CHECK (default false): skip rewrite rules whose
//     RHS grows beyond RewriteOptions::max_expression_growth.
//   * REJECT_DUPLICATE_LHS / REJECT_CONFLICTING_LHS (default false): opt into
//     dropping duplicate or conflicting rewrite candidates.
//   * ENABLE_REWRITE_SINGULAR_NF (default true): allow Singular-backed zero
//     checks during rewrite normalization.
//   * DISABLE_REWRITE_CACHE / VERIFY_REWRITE_LOOKUPS (default false): debug
//     cache/memo correctness by disabling or rechecking rewrite memo hits.
static bool PRESERVE_EQMODP1_VARS = false;
static bool ENABLE_SUBEXPRESSION_RULES = false;
static bool ENABLE_EXPRESSION_GROWTH_CHECK = false;
static bool REJECT_DUPLICATE_LHS = false;
static bool REJECT_CONFLICTING_LHS = false;
static bool ENABLE_REWRITE_SINGULAR_NF = true;
static bool DISABLE_REWRITE_CACHE = false;
static bool VERIFY_REWRITE_LOOKUPS = false;
static bool ENABLE_AUTO_LEMMAS = false;
static bool ENABLE_FINAL_FIXED_VALUE_CHECK = true;

struct AccumulatedTiming
{
    std::size_t calls = 0;
    std::chrono::nanoseconds elapsed{0};

    void reset()
    {
        calls = 0;
        elapsed = std::chrono::nanoseconds{0};
    }

    template <class Rep, class Period>
    void add(std::chrono::duration<Rep, Period> d)
    {
        ++calls;
        elapsed += std::chrono::duration_cast<std::chrono::nanoseconds>(d);
    }
};

static AccumulatedTiming g_groebner_timing;
static AccumulatedTiming g_final_fixed_value_check_timing;
static std::optional<clk::time_point> g_final_fixed_value_check_span_start;

class ScopedAccumulatedTiming
{
    AccumulatedTiming &timing_;
    clk::time_point start_;

public:
    explicit ScopedAccumulatedTiming(AccumulatedTiming &timing)
        : timing_(timing), start_(clk::now())
    {
        if (&timing_ == &g_final_fixed_value_check_timing &&
            !g_final_fixed_value_check_span_start)
        {
            g_final_fixed_value_check_span_start = start_;
        }
    }

    ~ScopedAccumulatedTiming()
    {
        timing_.add(clk::now() - start_);
    }
};

struct CliSummary
{
    std::string input_file;
    std::string options;
    std::chrono::nanoseconds parse_time{0};
    std::chrono::nanoseconds rewrite_time{0};
    std::chrono::nanoseconds solve_time{0};
    std::chrono::nanoseconds total_time{0};
    std::size_t groebner_calls = 0;
    std::chrono::nanoseconds groebner_time{0};
    std::size_t final_fixed_value_check_calls = 0;
    std::chrono::nanoseconds final_fixed_value_check_time{0};
    check_result result = unknown;
};

static std::string fmt_cli_seconds(std::chrono::nanoseconds d)
{
    const double seconds = std::chrono::duration<double>(d).count();
    std::ostringstream oss;
    oss << std::fixed << std::setprecision(4) << seconds << " seconds";
    return oss.str();
}

static std::string check_result_name(check_result r)
{
    switch (r)
    {
    case sat:
        return "sat";
    case unsat:
        return "unsat";
    case unknown:
        return "unknown";
    }
    return "unknown";
}

static void print_cli_value_row(std::ostream &os, const std::string &label, const std::string &value)
{
    os << std::left << std::setw(49) << label << value << "\n";
}

static void begin_cli_timed_row(std::ostream &os, const std::string &label)
{
    os << std::left << std::setw(49) << label;
    os.flush();
}

static void finish_cli_timed_row(std::ostream &os,
                                 const std::string &status,
                                 std::chrono::nanoseconds elapsed,
                                 std::optional<std::size_t> calls = std::nullopt)
{
    std::ostringstream state;
    state << "[" << status << "]";
    if (calls)
        state << " " << *calls << " calls";

    os << std::left << std::setw(28) << state.str()
       << fmt_cli_seconds(elapsed) << "\n";
    os.flush();
}

static void print_cli_input_section(std::ostream &os, const std::string &input_file, const std::string &options)
{
    os << "# Input\n\n";
    print_cli_value_row(os, "Input file:", input_file);
    print_cli_value_row(os, "Options:", options);
    os << "\n# Procedure main\n\n";
    os.flush();
}

static std::string join_options(int argc, char **argv)
{
    if (argc <= 2)
        return "(none)";

    std::ostringstream oss;
    for (int i = 2; i < argc; ++i)
    {
        if (i > 2)
            oss << ' ';
        oss << argv[i];
    }
    return oss.str();
}

static void print_usage(std::ostream &os, const char *prog)
{
    os << "Usage: " << prog
       << " <input.smt2> [--ring-detail] [--env] [--no-trace]"
          " [--disable-all-false] [--disable-all-true] [--disable-mixed]"
          " [--m-prime] [--disable-auto-lemmas]"
          " [--no-rewriting] [--no-singular-nf]"
          " [--preserve-eqmodp1-vars] [--enable-subexpression-rules]"
          " [--enable-expression-growth-check]"
          " [--reject-duplicate-lhs] [--reject-conflicting-lhs]"
          " [--disable-rewrite-cache] [--verify-rewrite-lookups]"
          " [--disable-final-fixed-value-check] [--show-model]"
          " [--rewrite-log]\n";
}

static void init_singular()
{
    (void)singular_shared_coeffs_Z();
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

    std::ostringstream oss;
    oss << label << " = {";
    bool first = true;
    for (int i = 0; i < I->ncols; ++i)
    {
        if (I->m[i] == nullptr)
            continue;
        if (!first)
            oss << ", ";
        char *s = p_String(I->m[i], R);
        oss << s;
        omFree(s);
        first = false;
    }
    oss << "}";
    LOG_INFO(g_log, "singular", oss.str());
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
static bool is_tracking_symbol_name(const std::string &name)
{
    if (name.size() < 3)
        return false;
    if (name[0] != 'A' || name[1] != '#')
        return false;
    for (size_t i = 2; i < name.size(); ++i)
    {
        if (!std::isdigit((unsigned char)name[i]))
            return false;
    }
    return true;
}

static void print_model_filtered(const z3::model &m, std::ostream &os = std::cout)
{
    os << "Model:\n";

    Z3_context c = (Z3_context)m.ctx();
    Z3_model zm = (Z3_model)m;

    for (unsigned i = 0; i < m.size(); ++i)
    {
        z3::func_decl fd = m[i];
        std::string name = fd.name().str();

        if (is_tracking_symbol_name(name))
            continue;

        if (fd.arity() != 0)
            continue;

        Z3_func_decl zfd = (Z3_func_decl)fd;
        Z3_ast ast = Z3_model_get_const_interp(c, zm, zfd);
        if (ast == nullptr)
            continue;

        z3::expr val(m.ctx(), ast);

        os << "(define-fun " << name
           << " () " << fd.range()
           << "\n  " << val
           << ")\n";
    }
}

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

static std::vector<expr> dedup_and_drop_trivial_eqp(const std::vector<expr> &eqps)
{
    std::vector<expr> out;
    out.reserve(eqps.size());
    std::unordered_set<std::string> seen;
    for (const auto &e : eqps)
    {
        if (!(e.is_app() && e.decl().name().str() == "eqP" && e.num_args() == 2))
            continue;
        if ((e.arg(0) == e.arg(1)).simplify().is_true())
            continue;
        if (seen.insert(e.to_string()).second)
            out.push_back(e);
    }
    return out;
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

// ---------------- collectors (used after rewriting for Singular lowering) -------------
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

static void collect_eqmodP2_rec(const expr &e, std::vector<expr> &atoms)
{
    if (!e.is_app())
        return;
    if (e.decl().name().str() == "eqmodP2" && e.num_args() == 4)
    {
        atoms.push_back(e);
        return;
    }
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_eqmodP2_rec(e.arg(i), atoms);
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

static poly copy_poly_or_null(poly p, const ring R)
{
    return p ? p_Copy(p, R) : nullptr;
}

static void delete_poly_if_nonnull(poly &p, const ring R)
{
    if (p)
        p_Delete(&p, R);
    p = nullptr;
}

static poly poly_mul_clone_or_zero(poly a, poly b, const ring R)
{
    if (!a || !b)
        return nullptr;
    return poly_mul_clone(a, b, R);
}

static poly poly_negate_owned(poly p, const ring R)
{
    if (!p)
        return nullptr;
    number neg1 = num_from_si(-1, R->cf);
    poly out = p_Mult_nn(p, neg1, R);
    n_Delete(&neg1, R->cf);
    return out;
}

static poly poly_add_owned(poly a, poly b, const ring R)
{
    if (!a)
        return b;
    if (!b)
        return a;
    return p_Add_q(a, b, R);
}

static poly poly_sub_product_clone(poly base, poly u, poly m, const ring R)
{
    poly out = copy_poly_or_null(base, R);
    poly um = poly_mul_clone_or_zero(u, m, R);
    poly neg_um = poly_negate_owned(um, R);
    return poly_add_owned(out, neg_um, R);
}

static poly build_eqmodP2_true_gen(poly D, poly U1, poly M1, poly U2, poly M2, const ring R)
{
    poly tmp = poly_sub_product_clone(D, U1, M1, R);
    poly out = poly_sub_product_clone(tmp, U2, M2, R);
    delete_poly_if_nonnull(tmp, R);
    return out;
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

        ord_heap[0] = ringorder_lp;
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

        poly base = polyterm_to_singular_poly(p.arg(0), env, indet_ring_names, RE, cmap, Nc, tag);

        if (k == 1)
            return base;

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

static ideal groebner_std(ideal I, const ring R, const std::string &label = "")
{
    rChangeCurrRing(R);
    auto t0 = clk::now();
    intvec *w0 = NULL;
    intvec **w = &w0;
    ideal G = kStd(I, NULL, testHomog, w, NULL, 0, 0, NULL);
    auto t1 = clk::now();
    g_groebner_timing.add(t1 - t0);

    std::ostringstream oss;
    oss << "Groebner basis std";
    if (!label.empty())
        oss << " [" << label << "]";
    oss << " finished in " << util::fmt_duration(t1 - t0);
    LOG_INFO(g_log, "singular", oss.str());
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

    LOG_TRACE(g_log, "singular", label + " LHS(poly) = " + poly_to_string(pA, R));
    LOG_TRACE(g_log, "singular", label + " RHS(poly) = " + poly_to_string(pB, R));

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

// ---------------- eqmodP2 compilation ----------------
struct EqModP2Compiled
{
    expr atom;
    expr A;
    expr B;
    expr M1term;
    expr M2term;

    poly D = nullptr;       // owned: D = A - B
    poly M1_poly = nullptr; // owned
    poly M2_poly = nullptr; // owned

    std::string u1_name;     // fresh quotient variable in ring
    std::string u2_name;     // fresh quotient variable in ring
    poly U1_poly = nullptr;  // owned: monomial u1
    poly U2_poly = nullptr;  // owned: monomial u2
    poly true_gen = nullptr; // owned: D - U1_poly*M1_poly - U2_poly*M2_poly
};

static EqModP2Compiled compile_eqmodP2_singular(const expr &atom,
                                                const expr &A,
                                                const expr &B,
                                                const expr &M1term,
                                                const expr &M2term,
                                                const std::string &label,
                                                const IndetEnv &env,
                                                const std::vector<std::string> &indet_ring_names,
                                                RingEnv &RE,
                                                const CoeffVarMap &cmap,
                                                int Nc,
                                                const std::string &u1_name,
                                                const std::string &u2_name)
{
    ring R = RE.R;
    rChangeCurrRing(R);

    EqModP2Compiled out{
        atom,
        A,
        B,
        M1term,
        M2term,
        nullptr,
        nullptr,
        nullptr,
        u1_name,
        u2_name,
        nullptr,
        nullptr,
        nullptr};

    poly pA = polyterm_to_singular_poly(A, env, indet_ring_names, RE, cmap, Nc, label + "/LHS");
    poly pB = polyterm_to_singular_poly(B, env, indet_ring_names, RE, cmap, Nc, label + "/RHS");
    out.D = poly_add_owned(pA, poly_negate_owned(pB, R), R);

    out.M1_poly = polyterm_to_singular_poly(M1term, env, indet_ring_names, RE, cmap, Nc, label + "/MOD1");
    out.M2_poly = polyterm_to_singular_poly(M2term, env, indet_ring_names, RE, cmap, Nc, label + "/MOD2");
    out.U1_poly = make_var_poly(RE, u1_name);
    out.U2_poly = make_var_poly(RE, u2_name);
    out.true_gen = build_eqmodP2_true_gen(out.D, out.U1_poly, out.M1_poly, out.U2_poly, out.M2_poly, R);

    LOG_INFO(g_log, "singular", label + " D(poly) = " + poly_to_string(out.D, R));
    LOG_INFO(g_log, "singular", label + " M1(poly) = " + poly_to_string(out.M1_poly, R));
    LOG_INFO(g_log, "singular", label + " M2(poly) = " + poly_to_string(out.M2_poly, R));
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
    std::vector<std::pair<std::string, std::string>> m_eqmodp2_qvar_names;

    int m_Nc = 0;
    int m_Mi = 0;

    std::vector<EqPCompiled> m_eqp;
    std::vector<EqModPCompiled> m_eqmodp;
    std::vector<EqModP2Compiled> m_eqmodp2;
    std::unordered_set<Z3_ast> m_compiled_eqmodp2_atoms;

    std::vector<poly> m_auto_zero_gens;
    std::vector<std::string> m_auto_zero_labels;

    std::unordered_map<Z3_ast, Z3_lbool> m_bool_cache;
    std::unordered_map<Z3_ast, Z3_ast> m_fixed_ast_cache;

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

    bool try_get_fixed_expr(const expr &t, expr &out) const
    {
        auto it = m_fixed_ast_cache.find((Z3_ast)t);
        if (it == m_fixed_ast_cache.end())
            return false;
        if (it->second == nullptr)
            return false;
        expr v(t.ctx(), it->second);
        out = v;
        return true;
    }

    void cache_fixed_expr(const expr &t, const expr &v)
    {
        Z3_ast key = (Z3_ast)t;
        Z3_ast val = (Z3_ast)v;
        if (key == nullptr || val == nullptr)
            return;

        auto it = m_fixed_ast_cache.find(key);
        if (it != m_fixed_ast_cache.end())
        {
            if (it->second == val)
                return;
            Z3_dec_ref((Z3_context)ctx(), it->second);
            it->second = val;
            Z3_inc_ref((Z3_context)ctx(), val);
            return;
        }

        m_fixed_ast_cache.emplace(key, val);
        Z3_inc_ref((Z3_context)ctx(), val);
    }

    static bool parse_z3_numeral_to_mpz(const expr &e, mpz_class &out)
    {
        if (!e.is_numeral())
            return false;
        Z3_string s = Z3_get_numeral_string((Z3_context)e.ctx(), (Z3_ast)e);
        mpz_class v;
        if (v.set_str(s, 10) != 0)
            return false;
        out = v;
        return true;
    }

    bool try_eval_bv_with_fixed_values(const expr &e, mpz_class &out) const
    {
        if (e.is_numeral() && e.get_sort().is_bv())
            return parse_z3_numeral_to_mpz(e, out);

        expr fv = e;
        if (try_get_fixed_expr(e, fv))
        {
            if (z3::eq(fv, e))
                return false;
            return try_eval_bv_with_fixed_values(fv, out);
        }

        return false;
    }

    bool try_eval_int_with_fixed_values(const expr &e, mpz_class &out) const
    {
        if (e.is_numeral() && e.get_sort().is_int())
            return parse_z3_numeral_to_mpz(e, out);

        expr fv = e;
        if (try_get_fixed_expr(e, fv))
        {
            if (z3::eq(fv, e))
                return false;
            return try_eval_int_with_fixed_values(fv, out);
        }

        if (!e.is_app())
            return false;

        const std::string op = e.decl().name().str();

        if (op == "-" && e.num_args() == 1)
        {
            mpz_class a;
            if (!try_eval_int_with_fixed_values(e.arg(0), a))
                return false;
            out = -a;
            return true;
        }

        if ((op == "+" || op == "-" || op == "*") && e.num_args() == 2)
        {
            mpz_class a, b;
            if (!try_eval_int_with_fixed_values(e.arg(0), a))
                return false;
            if (!try_eval_int_with_fixed_values(e.arg(1), b))
                return false;

            if (op == "+")
                out = a + b;
            else if (op == "-")
                out = a - b;
            else
                out = a * b;
            return true;
        }

        if (is_bv_to_int_app(e) && e.num_args() == 1)
        {
            mpz_class bv;
            if (!try_eval_bv_with_fixed_values(e.arg(0), bv))
                return false;
            out = bv;
            return true;
        }

        return false;
    }

    bool try_eval_polyterm_with_fixed_values(const expr &p, mpz_class &out) const
    {
        if (is_ctor(p, "PConst", 1))
            return try_eval_int_with_fixed_values(p.arg(0), out);

        if (is_ctor(p, "PNeg", 1))
        {
            mpz_class a;
            if (!try_eval_polyterm_with_fixed_values(p.arg(0), a))
                return false;
            out = -a;
            return true;
        }
        if (is_ctor(p, "PAdd", 2))
        {
            mpz_class a, b;
            if (!try_eval_polyterm_with_fixed_values(p.arg(0), a))
                return false;
            if (!try_eval_polyterm_with_fixed_values(p.arg(1), b))
                return false;
            out = a + b;
            return true;
        }
        if (is_ctor(p, "PSub", 2))
        {
            mpz_class a, b;
            if (!try_eval_polyterm_with_fixed_values(p.arg(0), a))
                return false;
            if (!try_eval_polyterm_with_fixed_values(p.arg(1), b))
                return false;
            out = a - b;
            return true;
        }
        if (is_ctor(p, "PMul", 2))
        {
            mpz_class a, b;
            if (!try_eval_polyterm_with_fixed_values(p.arg(0), a))
                return false;
            if (!try_eval_polyterm_with_fixed_values(p.arg(1), b))
                return false;
            out = a * b;
            return true;
        }
        if (is_ctor(p, "PPow", 2))
        {
            int64_t k = 0;
            if (!get_int64_numeral(p.arg(1), k) || k < 0)
                return false;
            mpz_class base;
            if (!try_eval_polyterm_with_fixed_values(p.arg(0), base))
                return false;
            mpz_class res = 1;
            for (int64_t i = 0; i < k; ++i)
                res *= base;
            out = res;
            return true;
        }

        return false;
    }

    static void collect_int_bv_subterms_rec(const expr &e,
                                            std::unordered_set<Z3_ast> &seen,
                                            std::vector<expr> &out)
    {
        if ((e.get_sort().is_int() || e.get_sort().is_bv()) && !e.is_numeral())
        {
            Z3_ast k = (Z3_ast)e;
            if (seen.insert(k).second)
                out.push_back(e);
        }
        for (unsigned i = 0; i < e.num_args(); ++i)
            collect_int_bv_subterms_rec(e.arg(i), seen, out);
    }

    static void collect_eval_terms_from_polyterm_rec(const expr &p,
                                                     std::unordered_set<Z3_ast> &seen,
                                                     std::vector<expr> &out)
    {
        if (is_ctor(p, "PConst", 1))
        {
            collect_int_bv_subterms_rec(p.arg(0), seen, out);
            return;
        }
        if (is_ctor(p, "PNeg", 1))
        {
            collect_eval_terms_from_polyterm_rec(p.arg(0), seen, out);
            return;
        }
        if (is_ctor(p, "PAdd", 2) || is_ctor(p, "PSub", 2) || is_ctor(p, "PMul", 2))
        {
            collect_eval_terms_from_polyterm_rec(p.arg(0), seen, out);
            collect_eval_terms_from_polyterm_rec(p.arg(1), seen, out);
            return;
        }
        if (is_ctor(p, "PPow", 2))
        {
            collect_eval_terms_from_polyterm_rec(p.arg(0), seen, out);
            collect_int_bv_subterms_rec(p.arg(1), seen, out);
            return;
        }
    }

    void register_eval_terms_for_eqmod_atom(const expr &A, const expr &B, const expr &M)
    {
        std::unordered_set<Z3_ast> seen;
        std::vector<expr> terms;
        collect_eval_terms_from_polyterm_rec(A, seen, terms);
        collect_eval_terms_from_polyterm_rec(B, seen, terms);
        collect_eval_terms_from_polyterm_rec(M, seen, terms);
        for (const auto &t : terms)
            this->add(t);
    }

    void register_eval_terms_for_eqmod_atom(const expr &A, const expr &B, const expr &M1, const expr &M2)
    {
        std::unordered_set<Z3_ast> seen;
        std::vector<expr> terms;
        collect_eval_terms_from_polyterm_rec(A, seen, terms);
        collect_eval_terms_from_polyterm_rec(B, seen, terms);
        collect_eval_terms_from_polyterm_rec(M1, seen, terms);
        collect_eval_terms_from_polyterm_rec(M2, seen, terms);
        for (const auto &t : terms)
            this->add(t);
    }

    void collect_fixed_ants_from_polyterm(const expr &p,
                                          std::unordered_set<Z3_ast> &seen,
                                          std::vector<expr> &ants) const
    {
        std::unordered_set<Z3_ast> eval_seen;
        std::vector<expr> eval_terms;
        collect_eval_terms_from_polyterm_rec(p, eval_seen, eval_terms);

        for (const auto &t : eval_terms)
        {
            expr v = t;
            if (!try_get_fixed_expr(t, v))
                continue;

            // Keep only terms that are concretely fixed now.
            if (!(v.is_numeral() || v.is_true() || v.is_false()))
                continue;

            Z3_ast k = (Z3_ast)t;
            if (seen.insert(k).second)
                ants.push_back(t);
        }
    }

    bool final_fixed_value_check_eqmodP1()
    {
        if (m_eqmodp.empty())
            return true;

        ring R = m_RE.R;
        rChangeCurrRing(R);

        for (auto &cp : m_eqmodp)
        {
            Z3_lbool bv = lbool_of(cp.atom);
            if (bv == Z3_L_UNDEF)
                continue;

            mpz_class a, b, m;
            bool ok_a = try_eval_polyterm_with_fixed_values(cp.A, a);
            bool ok_b = try_eval_polyterm_with_fixed_values(cp.B, b);
            bool ok_m = try_eval_polyterm_with_fixed_values(cp.Mterm, m);
            if (!(ok_a && ok_b && ok_m))
            {
                LOG_INFO(g_log, "singular",
                         "[eqmodP1] final fixed-value check conflict: " + label_of(cp.atom) +
                             " ; reason=insufficient fixed values for A/B/M evaluation");
                conflict_with({cp.atom});
                return false;
            }

            bool semantic_truth = false;
            mpz_class d = a - b;

            if (m == 0)
            {
                semantic_truth = (a == b);
            }
            else
            {
                poly pM = poly_from_mpz(m, R);
                poly pD = poly_from_mpz(d, R);

                std::vector<poly> gens;
                gens.push_back(pM);
                ideal I = ideal_from_polys(gens, m_RE);
                ideal G = groebner_std(I, R, "final-fixed-value-check");
                poly nf = kNF(G, NULL, pD, 0, 0);

                semantic_truth = nf_is_zero(nf);

                if (nf)
                    p_Delete(&nf, R);
                if (pD)
                    p_Delete(&pD, R);
                if (G)
                    idDelete(&G);
                if (I)
                    idDelete(&I);
            }

            bool assigned_truth = (bv == Z3_L_TRUE);
            if (assigned_truth != semantic_truth)
            {
                LOG_INFO(g_log, "singular",
                         "[eqmodP1] final fixed-value check conflict: " + label_of(cp.atom) +
                             " ; a=" + a.get_str() +
                             " ; b=" + b.get_str() +
                             " ; m=" + m.get_str() +
                             " ; assigned=" + std::string(assigned_truth ? "true" : "false") +
                             " ; semantic=" + std::string(semantic_truth ? "true" : "false"));

                std::vector<expr> ants;
                ants.push_back(cp.atom);

                std::unordered_set<Z3_ast> seen;
                seen.insert((Z3_ast)cp.atom);
                collect_fixed_ants_from_polyterm(cp.A, seen, ants);
                collect_fixed_ants_from_polyterm(cp.B, seen, ants);
                collect_fixed_ants_from_polyterm(cp.Mterm, seen, ants);

                conflict_with(ants);
                return false;
            }
        }

        return true;
    }

    bool final_fixed_value_check_eqmodP2()
    {
        if (m_eqmodp2.empty())
            return true;

        ring R = m_RE.R;
        rChangeCurrRing(R);

        for (auto &cp : m_eqmodp2)
        {
            Z3_lbool bv = lbool_of(cp.atom);
            if (bv == Z3_L_UNDEF)
                continue;

            mpz_class a, b, m1, m2;
            bool ok_a = try_eval_polyterm_with_fixed_values(cp.A, a);
            bool ok_b = try_eval_polyterm_with_fixed_values(cp.B, b);
            bool ok_m1 = try_eval_polyterm_with_fixed_values(cp.M1term, m1);
            bool ok_m2 = try_eval_polyterm_with_fixed_values(cp.M2term, m2);
            if (!(ok_a && ok_b && ok_m1 && ok_m2))
            {
                LOG_INFO(g_log, "singular",
                         "[eqmodP2] final fixed-value check skip: " + label_of(cp.atom) +
                             " ; reason=insufficient fixed values for A/B/M1/M2 evaluation");
                continue;
            }

            mpz_class d = a - b;
            bool semantic_truth = false;
            if (d == 0)
            {
                semantic_truth = true;
            }
            else if (m1 == 0 && m2 == 0)
            {
                semantic_truth = false;
            }
            else
            {
                std::vector<poly> gens;
                if (m1 != 0)
                    gens.push_back(poly_from_mpz(m1, R));
                if (m2 != 0)
                    gens.push_back(poly_from_mpz(m2, R));

                poly pD = poly_from_mpz(d, R);
                ideal I = ideal_from_polys(gens, m_RE);
                ideal G = groebner_std(I, R, "final-fixed-value-check-eqmodP2");
                poly nf = kNF(G, NULL, pD, 0, 0);

                semantic_truth = nf_is_zero(nf);

                delete_poly_if_nonnull(nf, R);
                delete_poly_if_nonnull(pD, R);
                if (G)
                    idDelete(&G);
                if (I)
                    idDelete(&I);
            }

            bool assigned_truth = (bv == Z3_L_TRUE);
            if (assigned_truth != semantic_truth)
            {
                LOG_INFO(g_log, "singular",
                         "[eqmodP2] final fixed-value check conflict: " + label_of(cp.atom) +
                             " ; a=" + a.get_str() +
                             " ; b=" + b.get_str() +
                             " ; m1=" + m1.get_str() +
                             " ; m2=" + m2.get_str() +
                             " ; assigned=" + std::string(assigned_truth ? "true" : "false") +
                             " ; semantic=" + std::string(semantic_truth ? "true" : "false"));

                std::vector<expr> ants;
                ants.push_back(cp.atom);

                std::unordered_set<Z3_ast> seen;
                seen.insert((Z3_ast)cp.atom);
                collect_fixed_ants_from_polyterm(cp.A, seen, ants);
                collect_fixed_ants_from_polyterm(cp.B, seen, ants);
                collect_fixed_ants_from_polyterm(cp.M1term, seen, ants);
                collect_fixed_ants_from_polyterm(cp.M2term, seen, ants);

                conflict_with(ants);
                return false;
            }
        }

        return true;
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

        for (auto &p : m_auto_zero_gens)
            if (p)
                gens.push_back(p_Copy(p, R));

        return gens;
    }

    void collect_true_eqp_generators(std::vector<poly> &gens_out, std::vector<expr> &ants_out)
    {
        ring R = m_RE.R;
        rChangeCurrRing(R);
        for (auto &ep : m_eqp)
        {
            if (ep.D_full == nullptr)
                continue;
            if (lbool_of(ep.atom) != Z3_L_TRUE)
                continue;
            gens_out.push_back(p_Copy(ep.D_full, R));
            ants_out.push_back(ep.atom);
        }
        for (auto &p : m_auto_zero_gens)
            if (p)
                gens_out.push_back(p_Copy(p, R));
    }

    void collect_true_eqmod_true_generators(std::vector<poly> &gens_out, std::vector<expr> &ants_out)
    {
        ring R = m_RE.R;
        rChangeCurrRing(R);
        for (auto &cp : m_eqmodp)
        {
            if (cp.true_gen == nullptr)
                continue;
            if (lbool_of(cp.atom) != Z3_L_TRUE)
                continue;
            gens_out.push_back(p_Copy(cp.true_gen, R));
            ants_out.push_back(cp.atom);
        }
    }

    void collect_true_eqmodp2_true_generators(std::vector<poly> &gens_out, std::vector<expr> &ants_out)
    {
        ring R = m_RE.R;
        rChangeCurrRing(R);
        for (auto &cp : m_eqmodp2)
        {
            if (lbool_of(cp.atom) != Z3_L_TRUE)
                continue;
            if (cp.true_gen != nullptr)
                gens_out.push_back(p_Copy(cp.true_gen, R));
            ants_out.push_back(cp.atom);
        }
    }

    bool query_membership_with_groebner(const std::vector<poly> &gens, poly target, std::string &nf_out,
                                        const std::string &ideal_label, const std::string &gb_label)
    {
        ring R = m_RE.R;
        rChangeCurrRing(R);

        ideal I = ideal_from_polys(gens, m_RE);
        print_ideal(ideal_label.c_str(), I, R);
        LOG_INFO(g_log, "singular", "Computing Groebner basis " + gb_label + " = std(" + ideal_label + ") ...");
        ideal G = groebner_std(I, R, gb_label);
        print_ideal(gb_label.c_str(), G, R);
        poly nf = kNF(G, NULL, p_Copy(target, R), 0, 0);
        bool in = nf_is_zero(nf);
        nf_out = poly_to_string(nf, R);

        if (nf)
            p_Delete(&nf, R);
        if (G)
            idDelete(&G);
        if (I)
            idDelete(&I);
        return in;
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

    // ---------------- auto-lemma saturation ----------------
    void clear_auto_zero_gens()
    {
        ring R = m_RE.R;
        if (R)
        {
            rChangeCurrRing(R);
            for (auto &p : m_auto_zero_gens)
                if (p)
                    p_Delete(&p, R);
        }
        m_auto_zero_gens.clear();
        m_auto_zero_labels.clear();
    }

    void saturate_auto_lemmas()
    {
        clear_auto_zero_gens();
        if (!ENABLE_AUTO_LEMMAS)
            return;

        ring R = m_RE.R;
        if (R == nullptr)
            return;
        rChangeCurrRing(R);

        std::vector<poly> base_gens;
        for (auto &ep : m_eqp)
        {
            if (ep.D_full != nullptr && lbool_of(ep.atom) == Z3_L_TRUE)
                base_gens.push_back(p_Copy(ep.D_full, R));
        }
        for (auto &cp : m_eqmodp)
        {
            if (cp.true_gen != nullptr && lbool_of(cp.atom) == Z3_L_TRUE)
                base_gens.push_back(p_Copy(cp.true_gen, R));
        }

        if (base_gens.empty())
            return;

        std::map<unsigned, std::vector<size_t>> width_groups;
        for (size_t i = 0; i < m_cmap.z3_bases.size(); ++i)
        {
            const z3::expr &base = m_cmap.z3_bases[i];
            if (!is_bv_to_int_app(base))
                continue;
            unsigned w = base.arg(0).get_sort().bv_size();
            if (w == 0 || w > 64)
                continue;
            width_groups[w].push_back(i);
        }

        if (width_groups.empty())
        {
            for (auto &g : base_gens)
                if (g)
                    p_Delete(&g, R);
            return;
        }

        LOG_INFO(g_log, "singular", "=== auto-lemma saturation begin ===");

        for (auto &kv : width_groups)
        {
            unsigned w = kv.first;
            mpz_class m_bound = mpz_class(1) << w;

            std::vector<poly> gens;
            gens.reserve(1 + base_gens.size());
            gens.push_back(poly_from_mpz(m_bound, R));
            for (auto g : base_gens)
                gens.push_back(p_Copy(g, R));

            ideal I = ideal_from_polys(gens, m_RE);
            ideal G = groebner_std(I, R);

            for (size_t idx : kv.second)
            {
                poly v_poly = make_var_poly(m_RE, m_cmap.ring_names[idx]);
                poly nf = kNF(G, NULL, p_Copy(v_poly, R), 0, 0);
                bool is_zero = nf_is_zero(nf);
                if (nf)
                    p_Delete(&nf, R);

                if (is_zero)
                {
                    m_auto_zero_gens.push_back(p_Copy(v_poly, R));
                    m_auto_zero_labels.push_back(m_cmap.ring_names[idx]);
                    LOG_INFO(g_log, "singular",
                             "[auto-lemma] implied zero: " + m_cmap.ring_names[idx] +
                                 " (bv width=" + std::to_string(w) + ")");
                }
                p_Delete(&v_poly, R);
            }

            if (G)
                idDelete(&G);
            if (I)
                idDelete(&I);
        }

        for (auto &g : base_gens)
            if (g)
                p_Delete(&g, R);

        LOG_INFO(g_log, "singular",
                 "=== auto-lemma saturation end (count=" +
                     std::to_string(m_auto_zero_gens.size()) + ") ===");
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

        ring R = m_RE.R;
        rChangeCurrRing(R);
        bool same_modulus = same_modulus_across_eqmodp();

        LOG_INFO(g_log, "singular", "=== eqmodP1(all-false) refutation begin ===");
        std::vector<expr> true_eqp_atoms;
        for (auto &ep : m_eqp)
        {
            if (lbool_of(ep.atom) != Z3_L_TRUE)
                continue;
            true_eqp_atoms.push_back(ep.atom);
        }

        if (same_modulus)
        {
            std::vector<poly> gens;
            gens.reserve(1 + m_eqp.size() + m_auto_zero_gens.size());
            gens.push_back(p_Copy(m_eqmodp[0].M_poly, R));
            for (auto &ep : m_eqp)
            {
                if (ep.D_full == nullptr)
                    continue;
                if (lbool_of(ep.atom) != Z3_L_TRUE)
                    continue;
                gens.push_back(p_Copy(ep.D_full, R));
            }
            for (auto &p : m_auto_zero_gens)
                if (p)
                    gens.push_back(p_Copy(p, R));

            LOG_INFO(g_log, "singular", "Using " + std::to_string((int)true_eqp_atoms.size()) + " TRUE eqP equation(s) in ideal.");

            ideal I = ideal_from_polys(gens, m_RE);
            print_ideal("I", I, R);

            LOG_INFO(g_log, "singular", "Computing Groebner basis G = std(I) ...");
            ideal G = groebner_std(I, R, "G_all_false");

            print_ideal("G", G, R);

            if (ALL_FALSE_ASSUME_M_PRIME)
            {
                // Product refutation under the assumption that R/<m> is an integral domain
                // (e.g., m is prime / irreducible polynomial).
                poly prod = nullptr;
                for (auto &cp : m_eqmodp)
                {
                    if (!prod)
                    {
                        prod = p_Copy(cp.D, R);
                    }
                    else
                    {
                        poly next = poly_mul_clone(prod, cp.D, R);
                        p_Delete(&prod, R);
                        prod = next;
                    }
                }

                poly nf = kNF(G, NULL, p_Copy(prod, R), 0, 0);
                bool in = nf_is_zero(nf);

                LOG_INFO(g_log, "singular",
                         "Product query: P=" + poly_to_string(prod, R) +
                             " ; NF_G(P)=" + poly_to_string(nf, R) +
                             " ; P ∈ <M, {TRUE eqP}>? " + std::string(in ? "YES" : "NO"));

                if (in)
                {
                    LOG_INFO(g_log, "singular",
                             "[eqmodP1] all-false product refute: P in <M, {TRUE eqP}>; all-false assignment is impossible");
                    std::vector<expr> ants;
                    ants.reserve(m_eqmodp.size() + true_eqp_atoms.size());
                    for (auto &cp : m_eqmodp)
                        ants.push_back(cp.atom);
                    for (auto &a : true_eqp_atoms)
                        ants.push_back(a);
                    conflict_with(ants);
                }

                if (nf)
                    p_Delete(&nf, R);
                if (prod)
                    p_Delete(&prod, R);
                if (G)
                    idDelete(&G);
                if (I)
                    idDelete(&I);

                LOG_INFO(g_log, "singular", "=== eqmodP1(all-false) refutation end ===");
                return;
            }

            bool hit = false;
            expr hit_atom = ctx().bool_val(false);

            for (auto &cp : m_eqmodp)
            {
                poly d = p_Copy(cp.D, R);
                poly nf = kNF(G, NULL, d, 0, 0);
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
            return;
        }

        LOG_INFO(g_log, "singular", "all-false uses different moduli; running per-instance checks");
        bool hit = false;
        expr hit_atom = ctx().bool_val(false);
        for (auto &cp : m_eqmodp)
        {
            std::vector<expr> eqp_ants;
            std::vector<poly> gens;
            gens.reserve(1 + m_eqp.size());
            gens.push_back(p_Copy(cp.M_poly, R));
            collect_true_eqp_generators(gens, eqp_ants);

            std::string nf_s;
            std::string idx = label_of(cp.atom);
            std::string i_label = "I_all_false_diff_" + idx;
            std::string g_label = "G_all_false_diff_" + idx;
            bool in = query_membership_with_groebner(gens, cp.D, nf_s, i_label, g_label);
            LOG_INFO(g_log, "singular",
                     "Different-moduli query instance: " + label_of(cp.atom) +
                         " ; D=" + poly_to_string(cp.D, R) +
                         " ; NF_<mf,TRUE_eqP>(D)=" + nf_s +
                         " ; D ∈ <m_f, {TRUE eqP}>? " + std::string(in ? "YES" : "NO"));
            if (in)
            {
                LOG_INFO(g_log, "singular",
                         "[eqmodP1] all-false(different-moduli) refute: " + label_of(cp.atom) +
                             " has D in <m_f, {TRUE eqP}>; cannot be FALSE");
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

        ring R = m_RE.R;
        rChangeCurrRing(R);
        bool same_modulus = same_modulus_across_eqmodp();

        LOG_INFO(g_log, "singular", "=== eqmodP1(all-true) refutation begin ===");
        std::vector<expr> ants;
        std::vector<poly> gens;
        if (same_modulus)
        {
            gens = collect_true_context_generators(ants);
            if (gens.empty())
                return;
            LOG_INFO(g_log, "singular", "all-true uses same modulus context");
        }
        else
        {
            collect_true_eqmod_true_generators(gens, ants);
            if (gens.empty())
                return;
            LOG_INFO(g_log, "singular", "all-true uses different moduli context: J=<p_t-u_t*m_t>");
        }

        ideal J = ideal_from_polys(gens, m_RE);
        print_ideal(same_modulus ? "J_all_true" : "J_all_true_diffmod", J, R);

        LOG_INFO(g_log, "singular", "Computing Groebner basis G = std(J) ...");
        ideal G = groebner_std(J, R, same_modulus ? "G_all_true" : "G_all_true_diffmod");

        print_ideal(same_modulus ? "G_all_true" : "G_all_true_diffmod", G, R);

        poly one = poly_from_si(1, R);
        poly nf = kNF(G, NULL, one, 0, 0);
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
            LOG_INFO(g_log, "singular",
                     same_modulus ? "[eqmodP1] all-true refute: 1 ∈ J"
                                  : "[eqmodP1] all-true(different-moduli) refute: 1 ∈ J");
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

        ring R = m_RE.R;
        rChangeCurrRing(R);
        bool same_modulus = same_modulus_across_eqmodp();

        LOG_INFO(g_log, "singular", "=== eqmodP1(mixed) refutation begin ===");
        if (same_modulus)
        {
            std::vector<expr> true_context_ants;
            std::vector<poly> gens = collect_true_context_generators(true_context_ants);
            if (gens.empty())
                return;

            ideal J = ideal_from_polys(gens, m_RE);
            print_ideal("J_mixed", J, R);

            LOG_INFO(g_log, "singular", "Computing Groebner basis G = std(J) ...");
            ideal G = groebner_std(J, R, "G_mixed");

            print_ideal("G_mixed", G, R);

            bool hit = false;
            expr hit_atom = ctx().bool_val(false);

            for (auto &cp : m_eqmodp)
            {
                if (lbool_of(cp.atom) != Z3_L_FALSE)
                    continue;

                poly d = p_Copy(cp.D, R);
                poly nf = kNF(G, NULL, d, 0, 0);
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
            return;
        }

        LOG_INFO(g_log, "singular", "mixed uses different moduli context");

        std::vector<expr> true_eqp_atoms;
        std::vector<poly> true_eqp_gens;
        collect_true_eqp_generators(true_eqp_gens, true_eqp_atoms);

        std::vector<expr> true_eqmod_atoms;
        std::vector<poly> true_eqmod_gens;
        collect_true_eqmod_true_generators(true_eqmod_gens, true_eqmod_atoms);

        std::vector<poly> base_gens;
        base_gens.reserve(true_eqp_gens.size() + true_eqmod_gens.size());
        for (auto p : true_eqp_gens)
            base_gens.push_back(p_Copy(p, R));
        for (auto p : true_eqmod_gens)
            base_gens.push_back(p_Copy(p, R));
        for (auto &p : true_eqp_gens)
            if (p)
                p_Delete(&p, R);
        for (auto &p : true_eqmod_gens)
            if (p)
                p_Delete(&p, R);

        bool hit = false;
        expr hit_atom = ctx().bool_val(false);
        for (auto &cp : m_eqmodp)
        {
            if (lbool_of(cp.atom) != Z3_L_FALSE)
                continue;

            std::vector<poly> gens;
            gens.reserve(base_gens.size() + 1);
            for (auto p : base_gens)
                gens.push_back(p_Copy(p, R));
            gens.push_back(p_Copy(cp.M_poly, R));

            std::string nf_s;
            std::string idx = label_of(cp.atom);
            std::string i_label = "I_mixed_diff_" + idx;
            std::string g_label = "G_mixed_diff_" + idx;
            bool in = query_membership_with_groebner(gens, cp.D, nf_s, i_label, g_label);
            LOG_INFO(g_log, "singular",
                     "MIXED different-moduli query: " + label_of(cp.atom) +
                         " ; D=" + poly_to_string(cp.D, R) +
                         " ; NF_<m_f,J>(D)=" + nf_s +
                         " ; D ∈ <m_f, J>? " + std::string(in ? "YES" : "NO"));
            if (in)
            {
                LOG_INFO(g_log, "singular",
                         "[eqmodP1] mixed(different-moduli) refute: " + label_of(cp.atom) +
                             " has D in <m_f, J>; cannot be FALSE");
                hit = true;
                hit_atom = cp.atom;
                break;
            }
        }

        if (hit)
        {
            std::vector<expr> ants;
            ants.reserve(true_eqp_atoms.size() + true_eqmod_atoms.size() + 1);
            for (auto &a : true_eqp_atoms)
                ants.push_back(a);
            for (auto &a : true_eqmod_atoms)
                ants.push_back(a);
            ants.push_back(hit_atom);
            conflict_with(ants);
        }
        for (auto &p : base_gens)
            if (p)
                p_Delete(&p, R);

        LOG_INFO(g_log, "singular", "=== eqmodP1(mixed) refutation end ===");
    }

    void check_eqmodP1_conflicts()
    {
        saturate_auto_lemmas();
        check_eqmodP1_all_false_refutation();
        check_eqmodP1_all_true_refutation();
        check_eqmodP1_mixed_refutation();
    }

    bool all_eqp_eqmodp_fixed() const
    {
        for (const auto &ep : m_eqp)
        {
            if (lbool_of(ep.atom) == Z3_L_UNDEF)
                return false;
        }
        for (const auto &cp : m_eqmodp)
        {
            if (lbool_of(cp.atom) == Z3_L_UNDEF)
                return false;
        }
        return true;
    }

    void check_eqmodP1_conflicts_when_ready()
    {
        if (m_eqmodp.empty())
            return;
        if (!all_eqp_eqmodp_fixed())
            return;
        check_eqmodP1_conflicts();
    }

    bool all_eqp_eqmodp2_fixed() const
    {
        for (const auto &ep : m_eqp)
        {
            if (lbool_of(ep.atom) == Z3_L_UNDEF)
                return false;
        }
        for (const auto &cp : m_eqmodp2)
        {
            if (lbool_of(cp.atom) == Z3_L_UNDEF)
                return false;
        }
        return true;
    }

    void check_eqmodP2_all_false_refutation()
    {
        if (!ENABLE_ALL_FALSE)
            return;
        if (m_eqmodp2.empty())
            return;
        if (!all_eqp_eqmodp2_fixed())
            return;

        for (auto &cp : m_eqmodp2)
        {
            if (lbool_of(cp.atom) != Z3_L_FALSE)
                return;
        }

        ring R = m_RE.R;
        rChangeCurrRing(R);

        LOG_INFO(g_log, "singular", "=== eqmodP2(all-false) refutation begin ===");

        struct ModPairGroup
        {
            size_t rep = 0;
            std::vector<size_t> members;
        };

        std::vector<ModPairGroup> groups;
        for (size_t i = 0; i < m_eqmodp2.size(); ++i)
        {
            auto &cp = m_eqmodp2[i];
            bool grouped = false;
            for (auto &g : groups)
            {
                auto &rep = m_eqmodp2[g.rep];
                if (poly_equal(cp.M1_poly, rep.M1_poly, R) &&
                    poly_equal(cp.M2_poly, rep.M2_poly, R))
                {
                    g.members.push_back(i);
                    grouped = true;
                    break;
                }
            }
            if (!grouped)
            {
                groups.push_back(ModPairGroup{i, {i}});
            }
        }

        std::vector<expr> eqp_ants;
        for (auto &ep : m_eqp)
        {
            if (lbool_of(ep.atom) == Z3_L_TRUE)
                eqp_ants.push_back(ep.atom);
        }

        for (const auto &group : groups)
        {
            auto &rep = m_eqmodp2[group.rep];
            std::vector<poly> gens;

            if (rep.M1_poly)
                gens.push_back(copy_poly_or_null(rep.M1_poly, R));
            if (rep.M2_poly)
                gens.push_back(copy_poly_or_null(rep.M2_poly, R));

            for (auto &ep : m_eqp)
            {
                if (lbool_of(ep.atom) != Z3_L_TRUE)
                    continue;
                if (ep.D_full == nullptr)
                    continue;
                gens.push_back(copy_poly_or_null(ep.D_full, R));
            }

            LOG_INFO(g_log, "singular",
                     "eqmodP2 all-false group: representative=" + label_of(rep.atom) +
                         " ; members=" + std::to_string(group.members.size()) +
                         " ; M1=" + poly_to_string(rep.M1_poly, R) +
                         " ; M2=" + poly_to_string(rep.M2_poly, R));

            if (gens.empty())
            {
                for (size_t idx : group.members)
                {
                    auto &cp = m_eqmodp2[idx];
                    bool in = cp.D == nullptr;
                    std::string nf_s = in ? "0" : poly_to_string(cp.D, R);

                    LOG_INFO(g_log, "singular",
                             "eqmodP2 all-false query: " + label_of(cp.atom) +
                                 " ; D=" + poly_to_string(cp.D, R) +
                                 " ; NF(D)=" + nf_s +
                                 " ; D ∈ <M1,M2,{TRUE eqP}>? " + std::string(in ? "YES" : "NO"));

                    if (in)
                    {
                        LOG_INFO(g_log, "singular",
                                 "[eqmodP2] all-false refute: " + label_of(cp.atom) +
                                     " has D in <M1,M2,{TRUE eqP}>; cannot be FALSE");
                        std::vector<expr> ants;
                        ants.reserve(1 + eqp_ants.size());
                        ants.push_back(cp.atom);
                        for (auto &a : eqp_ants)
                            ants.push_back(a);
                        conflict_with(ants);
                        LOG_INFO(g_log, "singular", "=== eqmodP2(all-false) refutation end ===");
                        return;
                    }
                }
                continue;
            }

            ideal I = ideal_from_polys(gens, m_RE);
            print_ideal("I_eqmodP2_all_false", I, R);

            LOG_INFO(g_log, "singular", "Computing Groebner basis G_eqmodP2_all_false = std(I_eqmodP2_all_false) ...");
            ideal G = groebner_std(I, R, "G_eqmodP2_all_false");
            print_ideal("G_eqmodP2_all_false", G, R);

            for (size_t idx : group.members)
            {
                auto &cp = m_eqmodp2[idx];
                bool in = false;
                std::string nf_s = "not-computed";

                if (cp.D == nullptr)
                {
                    in = true;
                    nf_s = "0";
                }
                else
                {
                    poly target = copy_poly_or_null(cp.D, R);
                    poly nf = kNF(G, NULL, target, 0, 0);
                    in = nf_is_zero(nf);
                    nf_s = poly_to_string(nf, R);

                    delete_poly_if_nonnull(nf, R);
                    delete_poly_if_nonnull(target, R);
                }

                LOG_INFO(g_log, "singular",
                         "eqmodP2 all-false query: " + label_of(cp.atom) +
                             " ; D=" + poly_to_string(cp.D, R) +
                             " ; NF(D)=" + nf_s +
                             " ; D ∈ <M1,M2,{TRUE eqP}>? " + std::string(in ? "YES" : "NO"));

                if (in)
                {
                    LOG_INFO(g_log, "singular",
                             "[eqmodP2] all-false refute: " + label_of(cp.atom) +
                                 " has D in <M1,M2,{TRUE eqP}>; cannot be FALSE");
                    std::vector<expr> ants;
                    ants.reserve(1 + eqp_ants.size());
                    ants.push_back(cp.atom);
                    for (auto &a : eqp_ants)
                        ants.push_back(a);
                    conflict_with(ants);
                    if (G)
                        idDelete(&G);
                    if (I)
                        idDelete(&I);
                    LOG_INFO(g_log, "singular", "=== eqmodP2(all-false) refutation end ===");
                    return;
                }
            }

            if (G)
                idDelete(&G);
            if (I)
                idDelete(&I);
        }

        LOG_INFO(g_log, "singular", "=== eqmodP2(all-false) refutation end ===");
    }

    void check_eqmodP2_all_true_refutation()
    {
        if (!ENABLE_ALL_TRUE)
            return;
        if (m_eqmodp2.empty())
            return;
        if (!all_eqp_eqmodp2_fixed())
            return;

        for (auto &cp : m_eqmodp2)
        {
            if (lbool_of(cp.atom) != Z3_L_TRUE)
                return;
        }

        ring R = m_RE.R;
        rChangeCurrRing(R);

        LOG_INFO(g_log, "singular", "=== eqmodP2(all-true) refutation begin ===");

        std::vector<expr> ants;
        std::vector<poly> gens;
        collect_true_eqp_generators(gens, ants);
        collect_true_eqmod_true_generators(gens, ants);
        collect_true_eqmodp2_true_generators(gens, ants);

        if (gens.empty())
        {
            LOG_INFO(g_log, "singular", "eqmodP2 all-true context is empty; 1 is not in the zero ideal");
            LOG_INFO(g_log, "singular", "=== eqmodP2(all-true) refutation end ===");
            return;
        }

        ideal J = ideal_from_polys(gens, m_RE);
        print_ideal("J_eqmodP2_all_true", J, R);

        LOG_INFO(g_log, "singular", "Computing Groebner basis G_eqmodP2_all_true = std(J_eqmodP2_all_true) ...");
        ideal G = groebner_std(J, R, "G_eqmodP2_all_true");
        print_ideal("G_eqmodP2_all_true", G, R);

        poly one = poly_from_si(1, R);
        poly nf = kNF(G, NULL, one, 0, 0);
        bool unsat = nf_is_zero(nf);

        LOG_INFO(g_log, "singular",
                 "eqmodP2 ALL-TRUE check: NF_G(1)=" + poly_to_string(nf, R) +
                     " ; 1 ∈ J ? " + std::string(unsat ? "YES" : "NO"));

        if (nf)
            p_Delete(&nf, R);
        if (G)
            idDelete(&G);
        if (J)
            idDelete(&J);

        if (unsat)
        {
            LOG_INFO(g_log, "singular",
                     "[eqmodP2] all-true refute: 1 ∈ <TRUE eqP, TRUE eqmodP1 true_gen, TRUE eqmodP2 true_gen, auto-zero>");
            conflict_with(ants);
        }

        LOG_INFO(g_log, "singular", "=== eqmodP2(all-true) refutation end ===");
    }

    void check_eqmodP2_mixed_refutation()
    {
        if (!ENABLE_MIXED)
            return;
        if (m_eqmodp2.empty())
            return;
        if (!all_eqp_eqmodp2_fixed())
            return;

        bool has_true = false;
        bool has_false = false;
        for (auto &cp : m_eqmodp2)
        {
            Z3_lbool bv = lbool_of(cp.atom);
            if (bv == Z3_L_TRUE)
                has_true = true;
            else if (bv == Z3_L_FALSE)
                has_false = true;
            else
                return;
        }

        if (!(has_true && has_false))
            return;

        ring R = m_RE.R;
        rChangeCurrRing(R);

        LOG_INFO(g_log, "singular", "=== eqmodP2(mixed) refutation begin ===");

        std::vector<expr> true_ants;
        std::vector<poly> base_gens;
        collect_true_eqp_generators(base_gens, true_ants);
        collect_true_eqmod_true_generators(base_gens, true_ants);
        collect_true_eqmodp2_true_generators(base_gens, true_ants);

        bool hit = false;
        expr hit_atom = ctx().bool_val(false);

        for (auto &cp : m_eqmodp2)
        {
            if (lbool_of(cp.atom) != Z3_L_FALSE)
                continue;

            std::vector<poly> gens;
            gens.reserve(base_gens.size() + 2);
            for (auto p : base_gens)
                gens.push_back(p_Copy(p, R));
            if (cp.M1_poly)
                gens.push_back(p_Copy(cp.M1_poly, R));
            if (cp.M2_poly)
                gens.push_back(p_Copy(cp.M2_poly, R));

            bool in = false;
            std::string nf_s;

            if (cp.D == nullptr)
            {
                in = true;
                nf_s = "0";
                if (!gens.empty())
                {
                    ideal I = ideal_from_polys(gens, m_RE);
                    if (I)
                        idDelete(&I);
                }
            }
            else if (gens.empty())
            {
                in = false;
                nf_s = poly_to_string(cp.D, R);
            }
            else
            {
                std::string idx = label_of(cp.atom);
                std::string i_label = "I_eqmodP2_mixed_" + idx;
                std::string g_label = "G_eqmodP2_mixed_" + idx;
                in = query_membership_with_groebner(gens, cp.D, nf_s, i_label, g_label);
            }

            LOG_INFO(g_log, "singular",
                     "eqmodP2 MIXED query: " + label_of(cp.atom) +
                         " ; D=" + poly_to_string(cp.D, R) +
                         " ; NF_<M1_f,M2_f,J>(D)=" + nf_s +
                         " ; D ∈ <M1_f,M2_f,J>? " + std::string(in ? "YES" : "NO"));

            if (in)
            {
                LOG_INFO(g_log, "singular",
                         "[eqmodP2] mixed refute: " + label_of(cp.atom) +
                             " has D in <M1_f,M2_f,J>; cannot be FALSE");
                hit = true;
                hit_atom = cp.atom;
                break;
            }
        }

        for (auto &p : base_gens)
            if (p)
                p_Delete(&p, R);

        if (hit)
        {
            std::vector<expr> ants = true_ants;
            ants.push_back(hit_atom);
            conflict_with(ants);
        }

        LOG_INFO(g_log, "singular", "=== eqmodP2(mixed) refutation end ===");
    }

    void check_eqmodP2_conflicts()
    {
        saturate_auto_lemmas();
        check_eqmodP2_all_false_refutation();
        check_eqmodP2_all_true_refutation();
        check_eqmodP2_mixed_refutation();
    }

    void check_eqmodP2_conflicts_when_ready()
    {
        if (m_eqmodp2.empty())
            return;
        if (!all_eqp_eqmodp2_fixed())
            return;
        check_eqmodP2_conflicts();
    }

    void check_eqmodP2_all_false_refutation_when_ready()
    {
        if (m_eqmodp2.empty())
            return;
        check_eqmodP2_all_false_refutation();
    }

public:
    PolyPropagator(solver *s,
                   const std::vector<expr> &eqps,
                   const std::vector<expr> &lhs,
                   const std::vector<expr> &rhs,
                   const std::vector<expr> &eqmodsP1,
                   const std::vector<expr> &eqmodsP2,
                   const IndetEnv &env,
                   const CoeffVarMap &cmap,
                   const std::vector<std::string> &indet_ring_names,
                   const std::vector<std::string> &ring_vars,
                   const std::vector<std::string> &qvar_names,
                   const std::vector<std::pair<std::string, std::string>> &eqmodp2_qvar_names)
        : user_propagator_base(s), m_env(env), m_cmap(cmap),
          m_indet_ring_names(indet_ring_names), m_ring_vars(ring_vars), m_qvar_names(qvar_names),
          m_eqmodp2_qvar_names(eqmodp2_qvar_names)
    {
        init_singular();

        register_fixed();
        register_final();
        register_created();

        m_Nc = (int)m_cmap.z3_bases.size();
        m_Mi = (int)m_env.names.size();

        coeffs cfZ = nCopyCoeff(singular_shared_coeffs_Z());

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
            register_eval_terms_for_eqmod_atom(em.arg(0), em.arg(1), em.arg(2));

            std::string label = "eqmodP1#" + std::to_string(i);
            m_label[(Z3_ast)em] = label;

            EqModPCompiled cp = compile_eqmodP1_singular(em, em.arg(0), em.arg(1), em.arg(2),
                                                         label,
                                                         m_env, m_indet_ring_names, m_RE, m_cmap,
                                                         m_Nc,
                                                         m_qvar_names[i]);
            m_eqmodp.push_back(std::move(cp));
        }

        if (m_eqmodp2_qvar_names.size() < eqmodsP2.size())
            throw std::runtime_error("eqmodp2_qvar_names size is smaller than eqmodsP2 size");

        for (size_t i = 0; i < eqmodsP2.size(); ++i)
        {
            auto &em = eqmodsP2[i];
            this->add(em);
            for (unsigned j = 0; j < 4; ++j)
                this->add(em.arg(j));
            register_eval_terms_for_eqmod_atom(em.arg(0), em.arg(1), em.arg(2), em.arg(3));

            std::string label = "eqmodP2#" + std::to_string(i);
            m_label[(Z3_ast)em] = label;

            const auto &qnames = m_eqmodp2_qvar_names[i];
            EqModP2Compiled cp = compile_eqmodP2_singular(em, em.arg(0), em.arg(1), em.arg(2), em.arg(3),
                                                          label,
                                                          m_env, m_indet_ring_names, m_RE, m_cmap,
                                                          m_Nc,
                                                          qnames.first,
                                                          qnames.second);
            m_compiled_eqmodp2_atoms.insert((Z3_ast)em);
            m_eqmodp2.push_back(std::move(cp));
        }
    }

    PolyPropagator(context &c,
                   const IndetEnv &env,
                   const CoeffVarMap &cmap,
                   const std::vector<std::string> &indet_ring_names,
                   const std::vector<std::string> &ring_vars,
                   const std::vector<std::string> &qvar_names,
                   const std::vector<std::pair<std::string, std::string>> &eqmodp2_qvar_names)
        : user_propagator_base(c), m_env(env), m_cmap(cmap),
          m_indet_ring_names(indet_ring_names), m_ring_vars(ring_vars), m_qvar_names(qvar_names),
          m_eqmodp2_qvar_names(eqmodp2_qvar_names)
    {
        init_singular();
        register_fixed();
        register_final();
        register_created();

        m_Nc = (int)m_cmap.z3_bases.size();
        m_Mi = (int)m_env.names.size();

        coeffs cfZ = nCopyCoeff(singular_shared_coeffs_Z());

        m_RE.build(cfZ, m_ring_vars, ringorder_lp);
    }

    ~PolyPropagator() override
    {
        for (auto &kv : m_fixed_ast_cache)
            if (kv.second != nullptr)
                Z3_dec_ref((Z3_context)ctx(), kv.second);
        m_fixed_ast_cache.clear();

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

            for (auto &cp : m_eqmodp2)
            {
                delete_poly_if_nonnull(cp.D, R);
                delete_poly_if_nonnull(cp.M1_poly, R);
                delete_poly_if_nonnull(cp.M2_poly, R);
                delete_poly_if_nonnull(cp.U1_poly, R);
                delete_poly_if_nonnull(cp.U2_poly, R);
                delete_poly_if_nonnull(cp.true_gen, R);
            }

            for (auto &ep : m_eqp)
            {
                if (ep.D_full)
                    p_Delete(&ep.D_full, R);
                ep.D_full = nullptr;
            }

            for (auto &p : m_auto_zero_gens)
                if (p)
                    p_Delete(&p, R);
            m_auto_zero_gens.clear();
            m_auto_zero_labels.clear();
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

            check_eqmodP1_conflicts_when_ready();
            check_eqmodP2_conflicts_when_ready();
            return;
        }

        if (t.decl().name().str() == "eqmodP1" && t.num_args() == 3)
        {
            expr A = t.arg(0), B = t.arg(1), M = t.arg(2);
            this->add(t);
            this->add(A);
            this->add(B);
            this->add(M);
            register_eval_terms_for_eqmod_atom(A, B, M);

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

            check_eqmodP1_conflicts_when_ready();
            check_eqmodP2_conflicts_when_ready();
            return;
        }

        if (t.decl().name().str() == "eqmodP2" && t.num_args() == 4)
        {
            if (m_compiled_eqmodp2_atoms.count((Z3_ast)t))
                return;

            expr A = t.arg(0), B = t.arg(1), M1 = t.arg(2), M2 = t.arg(3);
            this->add(t);
            this->add(A);
            this->add(B);
            this->add(M1);
            this->add(M2);
            register_eval_terms_for_eqmod_atom(A, B, M1, M2);

            size_t idx = m_eqmodp2.size();
            if (idx >= m_eqmodp2_qvar_names.size())
                throw std::runtime_error("created(eqmodP2): no preallocated qvar names; ensure all eqmodP2 are present in input SMT2");

            std::string label = "eqmodP2#" + std::to_string((int)idx);
            m_label[(Z3_ast)t] = label;

            const auto &qnames = m_eqmodp2_qvar_names[idx];
            EqModP2Compiled cp = compile_eqmodP2_singular(t, A, B, M1, M2,
                                                          label,
                                                          m_env, m_indet_ring_names, m_RE, m_cmap,
                                                          m_Nc,
                                                          qnames.first,
                                                          qnames.second);
            m_compiled_eqmodp2_atoms.insert((Z3_ast)t);
            m_eqmodp2.push_back(std::move(cp));

            check_eqmodP2_conflicts_when_ready();
            return;
        }
    }

    void fixed(const expr &t, const expr &v) override
    {
        ScopedAccumulatedTiming timing(g_final_fixed_value_check_timing);
        log_fixed(t, v);
        cache_fixed_expr(t, v);

        if (t.is_numeral())
            return;

        if (t.is_bool())
        {
            Z3_lbool bv = Z3_get_bool_value(ctx(), (Z3_ast)v);
            m_bool_cache[(Z3_ast)t] = bv;

            if (t.is_app() && t.decl().name().str() == "eqP" && t.num_args() == 2)
            {
                on_fixed_eqP(t, bv);
                check_eqmodP1_conflicts_when_ready();
                check_eqmodP2_conflicts_when_ready();
            }

            if (t.is_app() && t.decl().name().str() == "eqmodP1" && t.num_args() == 3)
            {
                check_eqmodP1_conflicts_when_ready();
                check_eqmodP2_conflicts_when_ready();
            }

            if (t.is_app() && t.decl().name().str() == "eqmodP2" && t.num_args() == 4)
            {
                check_eqmodP2_conflicts_when_ready();
            }
        }
    }

    void final() override
    {
        // check_eqmodP1_conflicts_when_ready();
        if (ENABLE_FINAL_FIXED_VALUE_CHECK)
        {
            ScopedAccumulatedTiming timing(g_final_fixed_value_check_timing);
            if (final_fixed_value_check_eqmodP1())
                final_fixed_value_check_eqmodP2();
        }
        std::cout << "===== [final] =====\n";
    }

    user_propagator_base *fresh(context &nctx) override
    {
        return new PolyPropagator(nctx, m_env, m_cmap, m_indet_ring_names, m_ring_vars, m_qvar_names, m_eqmodp2_qvar_names);
    }
};

int main(int argc, char **argv)
{
    // Self-test mode: bypass the file pipeline entirely.
    for (int i = 1; i < argc; ++i)
    {
        if (std::string(argv[i]) == "--selftest")
            return run_rewrite_selftests();
    }

    std::ofstream runlog("run.log", std::ios::out | std::ios::trunc);
    if (!runlog.is_open())
    {
        std::cerr << "Error: cannot open run.log for writing\n";
        return 1;
    }

    std::ostream terminal_out(std::cout.rdbuf());
    bool show_model_on_terminal = false;
    bool rewrite_log_requested = false;

    try
    {
        if (argc < 2)
        {
            print_usage(std::cerr, argv[0]);
            runlog << "Usage requested: missing input file\n";
            return 1;
        }

        for (int i = 2; i < argc; ++i)
        {
            std::string a = argv[i];
            if (a == "--ring-detail")
                PRINT_RING_DETAIL = true;
            else if (a == "--env")
                ENV = true;
            else if (a == "--no-trace")
                g_log.set_global(util::LogLevel::Debug);
            else if (a == "--disable-all-false")
                ENABLE_ALL_FALSE = false;
            else if (a == "--disable-all-true")
                ENABLE_ALL_TRUE = false;
            else if (a == "--disable-mixed")
                ENABLE_MIXED = false;
            else if (a == "--m-prime")
                ALL_FALSE_ASSUME_M_PRIME = true;
            else if (a == "--no-rewriting")
                ENABLE_REWRITING = false;
            else if (a == "--no-singular-nf")
                ENABLE_REWRITE_SINGULAR_NF = false;
            else if (a == "--preserve-eqmodp1-vars")
                PRESERVE_EQMODP1_VARS = true;
            else if (a == "--enable-subexpression-rules")
                ENABLE_SUBEXPRESSION_RULES = true;
            else if (a == "--enable-expression-growth-check")
                ENABLE_EXPRESSION_GROWTH_CHECK = true;
            else if (a == "--reject-duplicate-lhs")
                REJECT_DUPLICATE_LHS = true;
            else if (a == "--reject-conflicting-lhs")
                REJECT_CONFLICTING_LHS = true;
            else if (a == "--disable-rewrite-cache")
                DISABLE_REWRITE_CACHE = true;
            else if (a == "--verify-rewrite-lookups")
                VERIFY_REWRITE_LOOKUPS = true;
            else if (a == "--disable-auto-lemmas")
                ENABLE_AUTO_LEMMAS = false;
            else if (a == "--disable-final-fixed-value-check")
                ENABLE_FINAL_FIXED_VALUE_CHECK = false;
            else if (a == "--show-model")
                show_model_on_terminal = true;
            else if (a == "--rewrite-log")
                rewrite_log_requested = true;
            else
            {
                std::cerr << "Unknown option: " << a << "\n";
                print_usage(std::cerr, argv[0]);
                runlog << "Unknown option: " << a << "\n";
                return 1;
            }
        }

        CliSummary summary;
        summary.input_file = argv[1];
        summary.options = join_options(argc, argv);
        std::string terminal_model;

        g_groebner_timing.reset();
        g_final_fixed_value_check_timing.reset();
        g_final_fixed_value_check_span_start.reset();

        const auto total_t0 = clk::now();
        print_cli_input_section(terminal_out, summary.input_file, summary.options);

        {
            ScopedStreamBuf redirect_cout(std::cout, runlog.rdbuf());
            ScopedStreamBuf redirect_cerr(std::cerr, runlog.rdbuf());

            LOG_TRACE(g_log, "parse", "Reading SMT2 file: " + std::string(argv[1]));
            LOG_INFO(g_log, "parse", "Reading SMT2 file: " + std::string(argv[1]));

            context c;

            begin_cli_timed_row(terminal_out, "Parsing SMT2 file:");
            auto parse_t0 = clk::now();
            std::string raw = read_file_all(argv[1]);
            std::string smt = inject_poly_eqP_eqmodP_if_missing(raw);
            std::vector<expr> asserts = parse_smt2_assertions(c, smt);
            auto parse_t1 = clk::now();
            summary.parse_time = std::chrono::duration_cast<std::chrono::nanoseconds>(parse_t1 - parse_t0);
            finish_cli_timed_row(terminal_out, "OK", summary.parse_time);

            LOG_TRACE(g_log, "parse", "Loaded " + std::to_string(asserts.size()) + " assertions.");

            RewriteOptions rwopt;
            rwopt.enable_rewriting = ENABLE_REWRITING;
            rwopt.use_singular_normalization = ENABLE_REWRITE_SINGULAR_NF;
            rwopt.use_subexpression_rules = ENABLE_SUBEXPRESSION_RULES;
            rwopt.preserve_eqmodp1_vars = PRESERVE_EQMODP1_VARS;
            rwopt.enable_expression_growth_check = ENABLE_EXPRESSION_GROWTH_CHECK;
            rwopt.reject_duplicate_lhs = REJECT_DUPLICATE_LHS;
            rwopt.reject_conflicting_lhs = REJECT_CONFLICTING_LHS;
            rwopt.disable_rewrite_cache = DISABLE_REWRITE_CACHE;
            rwopt.verify_rewrite_lookups = VERIFY_REWRITE_LOOKUPS;

            std::ofstream rewrite_log;
            if (rewrite_log_requested)
            {
                rewrite_log.open("rewrite.log", std::ios::out | std::ios::trunc);
                if (!rewrite_log.is_open())
                    throw std::runtime_error("cannot open rewrite.log for writing");
                rwopt.rewrite_log = &rewrite_log;
            }
            std::ofstream rewrite_lookup_log;
            if (VERIFY_REWRITE_LOOKUPS)
            {
                rewrite_lookup_log.open("rewritelookups.log", std::ios::out | std::ios::trunc);
                if (!rewrite_lookup_log.is_open())
                    throw std::runtime_error("cannot open rewritelookups.log for writing");
                rwopt.rewrite_lookup_log = &rewrite_lookup_log;
            }

            begin_cli_timed_row(terminal_out, "Rewriting assignments:");
            auto rewrite_t0 = clk::now();
            RewriteResult rr = run_rewriting_pipeline(c, asserts, rwopt, g_log);
            auto rewrite_t1 = clk::now();
            summary.rewrite_time = std::chrono::duration_cast<std::chrono::nanoseconds>(rewrite_t1 - rewrite_t0);
            asserts = std::move(rr.asserts);
            finish_cli_timed_row(terminal_out, "OK", summary.rewrite_time);

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
            eqps = dedup_and_drop_trivial_eqp(eqps);

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

            std::vector<expr> eqmodsP2;
            for (auto &f : asserts)
                collect_eqmodP2_rec(f, eqmodsP2);

            for (size_t i = 0; i < eqmodsP2.size(); ++i)
            {
                LOG_TRACE(g_log, "parse",
                          "Found eqmodP2#" + std::to_string(i) +
                              " constraint: " + eqmodsP2[i].to_string());
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

            std::sort(bases.begin(), bases.end(),
                      [](const z3::expr &x, const z3::expr &y)
                      { return x.to_string() < y.to_string(); });

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
                qvar_names[i] = make_unique_name("u_mod_0_" + std::to_string(i), used);
            }

            std::vector<std::pair<std::string, std::string>> eqmodp2_qvar_names(eqmodsP2.size());
            for (size_t i = 0; i < eqmodsP2.size(); ++i)
            {
                eqmodp2_qvar_names[i].first = make_unique_name("u_mod_1_" + std::to_string(i) + "_0", used);
                eqmodp2_qvar_names[i].second = make_unique_name("u_mod_1_" + std::to_string(i) + "_1", used);
            }

            std::vector<std::string> ring_vars;
            ring_vars.reserve(cmap.ring_names.size() + indet_ring_names.size() + qvar_names.size() + 2 * eqmodp2_qvar_names.size());
            ring_vars.insert(ring_vars.end(), cmap.ring_names.begin(), cmap.ring_names.end());
            ring_vars.insert(ring_vars.end(), indet_ring_names.begin(), indet_ring_names.end());
            ring_vars.insert(ring_vars.end(), qvar_names.begin(), qvar_names.end());
            for (const auto &qnames : eqmodp2_qvar_names)
            {
                ring_vars.push_back(qnames.first);
                ring_vars.push_back(qnames.second);
            }

            LOG_TRACE(g_log, "init",
                      "Initializing propagator with " +
                          std::to_string(eqps.size()) + " eqP constraint(s), " +
                          std::to_string(eqmodsP1.size()) + " eqmodP1 constraint(s), " +
                          std::to_string(eqmodsP2.size()) + " eqmodP2 constraint(s).");

            PolyPropagator up(&s, eqps, lhs, rhs, eqmodsP1, eqmodsP2,
                              env, cmap, indet_ring_names, ring_vars, qvar_names, eqmodp2_qvar_names);

            begin_cli_timed_row(terminal_out, "Solving with Z3:");
            auto solve_t0 = clk::now();
            check_result r = s.check();
            auto solve_t1 = clk::now();
            summary.solve_time = std::chrono::duration_cast<std::chrono::nanoseconds>(solve_t1 - solve_t0);
            summary.result = r;
            finish_cli_timed_row(terminal_out, "OK", summary.solve_time);

            std::cout << "Solver result: " << r << "\n";
            if (r == unknown)
                std::cout << "Reason unknown: " << s.reason_unknown() << "\n";
            if (SHOW_MODEL && r == sat)
            {
                print_model_filtered(s.get_model());
                if (show_model_on_terminal)
                {
                    std::ostringstream model_out;
                    print_model_filtered(s.get_model(), model_out);
                    terminal_model = model_out.str();
                }
            }

            std::cout << "[timer] z3.check() = " << util::fmt_duration(solve_t1 - solve_t0) << "\n";
            std::cout.flush();
            std::cerr.flush();

            summary.groebner_calls = g_groebner_timing.calls;
            summary.groebner_time = g_groebner_timing.elapsed;
            summary.final_fixed_value_check_calls = g_final_fixed_value_check_timing.calls;
            if (g_final_fixed_value_check_span_start)
            {
                summary.final_fixed_value_check_time =
                    std::chrono::duration_cast<std::chrono::nanoseconds>(solve_t1 - *g_final_fixed_value_check_span_start);
            }
            else
            {
                summary.final_fixed_value_check_time = g_final_fixed_value_check_timing.elapsed;
            }
            summary.total_time = std::chrono::duration_cast<std::chrono::nanoseconds>(clk::now() - total_t0);
            runlog.flush();
        }

        begin_cli_timed_row(terminal_out, "   Computing Groebner basis:");
        finish_cli_timed_row(terminal_out, "OK", summary.groebner_time, summary.groebner_calls);
        terminal_out << "\n";
        begin_cli_timed_row(terminal_out, "   Final fixed-value check:");
        finish_cli_timed_row(terminal_out, "OK",
                             summary.final_fixed_value_check_time,
                             summary.final_fixed_value_check_calls);
        terminal_out << "\n# Summary\n\n";
        begin_cli_timed_row(terminal_out, "Verification result:");
        finish_cli_timed_row(terminal_out, check_result_name(summary.result), summary.total_time);
        if (show_model_on_terminal && !terminal_model.empty())
            terminal_out << "\n" << terminal_model;
        terminal_out.flush();
        return 0;
    }
    catch (const z3::exception &ex)
    {
        runlog << "Z3 error: " << ex.msg() << "\n";
        runlog.flush();
        std::cerr << "\n";
        std::cerr << "Z3 error: " << ex.msg() << "\n";
        return 1;
    }
    catch (const std::exception &ex)
    {
        runlog << "Error: " << ex.what() << "\n";
        runlog.flush();
        std::cerr << "\n";
        std::cerr << "Error: " << ex.what() << "\n";
        return 1;
    }
}
