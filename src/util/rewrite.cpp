#include "util/rewrite.hpp"

#include <z3.h>
#include <Singular/libsingular.h>

#include <algorithm>
#include <cctype>
#include <chrono>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iostream>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "util/fmt_duration.hpp"
#include "util/logger.hpp"

using namespace z3;

coeffs singular_shared_coeffs_Z()
{
    static bool singular_si_ready = false;
    if (!singular_si_ready)
    {
        const char *envp = std::getenv("SINGULAR_PATH");
        const char *path = envp ? envp : "/usr/bin/Singular";
        siInit((char *)path);
        singular_si_ready = true;
    }

    static coeffs cfZ = nullptr;
    if (!cfZ)
    {
        cfZ = nInitChar(n_Z, nullptr);
        if (!cfZ)
            throw std::runtime_error("Singular n_Z coefficient ring unavailable");
        // Keep the ℤ domain allocated for process lifetime — transient rings use
        // nCopyCoeff and rDelete paired decrements otherwise nKillChar the domain.
        nCopyCoeff(cfZ);
    }
    return cfZ;
}

RewriteRule::RewriteRule(const z3::expr &lhs_,
                         const z3::expr &rhs_,
                         const z3::expr &source_,
                         Kind kind_,
                         bool modular_,
                         std::string label_)
    : lhs(lhs_), rhs(rhs_), source_generator(source_), kind(kind_), is_modular(modular_),
      source_label(std::move(label_))
{
}

RewriteResult::RewriteResult(const z3::expr &target) : rewritten_target(target) {}

AnnotatedPolynomial::AnnotatedPolynomial(const z3::expr &poly, std::string annot)
    : polynomial(poly), annotation(std::move(annot))
{
}

AnnotatedPostcondition::AnnotatedPostcondition(const z3::expr &post,
                                               const z3::expr &poly,
                                               std::vector<z3::expr> ms,
                                               std::string annot)
    : postcondition(post), polynomial(poly), moduli(std::move(ms)), annotation(std::move(annot))
{
}

std::string rule_rhs_pretty(const PolyRewriteRule &rr)
{
    switch (rr.kind)
    {
    case PolyRewriteRule::Kind::ToZero:
        return "0";
    case PolyRewriteRule::Kind::ToConst:
        return rr.const_value.get_str();
    case PolyRewriteRule::Kind::Alias:
        return rr.target;
    case PolyRewriteRule::Kind::ExprRhs:
        return rr.rhs_int ? rr.rhs_int->to_string() : std::string("<poly-expr>");
    }
    return "<unknown>";
}

std::string pretty_rewrite_atom_name(const std::string &s)
{
    auto unwrap = [&](const char *prefix) -> std::string
    {
        const std::size_t plen = std::strlen(prefix);
        if (s.size() > plen + 1 && s.rfind(prefix, 0) == 0 && s.back() == ')')
            return s.substr(plen, s.size() - plen - 1);
        return {};
    };

    std::string u = unwrap("(ubv_to_int ");
    if (!u.empty())
        return u;
    u = unwrap("(sbv_to_int ");
    if (!u.empty())
        return u;
    u = unwrap("(bv2int ");
    if (!u.empty())
        return u;
    if (s.rfind("PConst:", 0) == 0)
        return s.substr(std::strlen("PConst:"));
    if (s.rfind("PVar:", 0) == 0)
        return s.substr(std::strlen("PVar:"));
    return s;
}

namespace
{

    struct CircularDependency : std::runtime_error
    {
        CircularDependency() : std::runtime_error("circular rewrite dependency") {}
    };

    bool same_ast(const expr &a, const expr &b)
    {
        if (&a.ctx() != &b.ctx())
            return false;
        return Z3_is_eq_ast((Z3_context)a.ctx(), (Z3_ast)a, (Z3_ast)b);
    }

    unsigned ast_id(const expr &e)
    {
        return Z3_get_ast_id((Z3_context)e.ctx(), (Z3_ast)e);
    }

    struct AstCacheKey
    {
        Z3_context ctx = nullptr;
        unsigned id = 0;

        bool operator==(const AstCacheKey &other) const
        {
            return ctx == other.ctx && id == other.id;
        }
    };

    struct AstCacheKeyHash
    {
        std::size_t operator()(const AstCacheKey &key) const
        {
            return std::hash<void *>{}((void *)key.ctx) ^ (std::hash<unsigned>{}(key.id) << 1);
        }
    };

    std::string expr_key(const expr &e)
    {
        return e.to_string();
    }

    bool is_ctor(const expr &e, const char *name, unsigned arity)
    {
        return e.is_app() && e.decl().name().str() == name && e.num_args() == arity;
    }

    bool is_poly_ctor(const expr &e)
    {
        if (!e.is_app())
            return false;
        const std::string n = e.decl().name().str();
        return n == "PConst" || n == "PVar" || n == "PNeg" || n == "PAdd" ||
               n == "PSub" || n == "PMul" || n == "PPow";
    }

    bool get_int64_numeral(const expr &e, int64_t &out)
    {
        if (!(e.is_numeral() && e.get_sort().is_int()))
            return false;
        return Z3_get_numeral_int64((Z3_context)e.ctx(), (Z3_ast)e, &out);
    }

    bool parse_mpz_numeral(const expr &e, mpz_class &out)
    {
        if (!(e.is_numeral() && e.get_sort().is_int()))
            return false;
        Z3_string s = Z3_get_numeral_string((Z3_context)e.ctx(), (Z3_ast)e);
        return out.set_str(s, 10) == 0;
    }

    expr int_val(context &ctx, const mpz_class &v)
    {
        return ctx.int_val(v.get_str().c_str());
    }

    bool get_string_literal_smt(const expr &e, std::string &out)
    {
        if (!Z3_is_string_sort((Z3_context)e.ctx(), (Z3_sort)e.get_sort()))
            return false;

        std::string s = e.to_string();
        if (s.size() < 2 || s.front() != '"' || s.back() != '"')
            return false;
        s = s.substr(1, s.size() - 2);

        std::string r;
        r.reserve(s.size());
        for (std::size_t i = 0; i < s.size(); ++i)
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
        out = std::move(r);
        return true;
    }

    bool is_bv_to_int_app(const z3::expr &e)
    {
        if (!e.is_app() || !e.get_sort().is_int() || e.num_args() != 1 || !e.arg(0).get_sort().is_bv())
            return false;
#ifdef Z3_OP_BV2INT
        if (e.decl().decl_kind() == Z3_OP_BV2INT)
            return true;
#endif
        const std::string n = e.decl().name().str();
        return n == "ubv_to_int" || n == "sbv_to_int" || n == "bv2nat" || n == "bv2int";
    }

    bool is_int_atom(const expr &e)
    {
        return e.get_sort().is_int() &&
               ((e.is_const() && !e.is_numeral()) || is_bv_to_int_app(e));
    }

    struct PolyDecls
    {
        Z3_func_decl pconst = nullptr;
        Z3_func_decl pvar = nullptr;
        Z3_func_decl pneg = nullptr;
        Z3_func_decl padd = nullptr;
        Z3_func_decl psub = nullptr;
        Z3_func_decl pmul = nullptr;
        Z3_func_decl ppow = nullptr;
        Z3_func_decl eqp = nullptr;
        Z3_func_decl eqmodp1 = nullptr;
    };

    void fill_poly_decls_from_sort(const expr &e, PolyDecls &d)
    {
        if (!is_poly_ctor(e))
            return;
        Z3_context c = (Z3_context)e.ctx();
        Z3_sort s = (Z3_sort)e.get_sort();
        unsigned n = Z3_get_datatype_sort_num_constructors(c, s);
        for (unsigned i = 0; i < n; ++i)
        {
            Z3_func_decl fd = Z3_get_datatype_sort_constructor(c, s, i);
            func_decl zfd(e.ctx(), fd);
            const std::string name = zfd.name().str();
            if (name == "PConst")
                d.pconst = fd;
            else if (name == "PVar")
                d.pvar = fd;
            else if (name == "PNeg")
                d.pneg = fd;
            else if (name == "PAdd")
                d.padd = fd;
            else if (name == "PSub")
                d.psub = fd;
            else if (name == "PMul")
                d.pmul = fd;
            else if (name == "PPow")
                d.ppow = fd;
        }
    }

    void collect_decls_rec(const expr &e, PolyDecls &d)
    {
        if (e.is_app())
        {
            fill_poly_decls_from_sort(e, d);
            const std::string n = e.decl().name().str();
            Z3_func_decl fd = (Z3_func_decl)e.decl();
            if (n == "PConst" && e.num_args() == 1)
                d.pconst = fd;
            else if (n == "PVar" && e.num_args() == 1)
                d.pvar = fd;
            else if (n == "PNeg" && e.num_args() == 1)
                d.pneg = fd;
            else if (n == "PAdd" && e.num_args() == 2)
                d.padd = fd;
            else if (n == "PSub" && e.num_args() == 2)
                d.psub = fd;
            else if (n == "PMul" && e.num_args() == 2)
                d.pmul = fd;
            else if (n == "PPow" && e.num_args() == 2)
                d.ppow = fd;
            else if (n == "eqP" && e.num_args() == 2)
                d.eqp = fd;
            else if (n == "eqmodP1" && e.num_args() == 3)
                d.eqmodp1 = fd;

            for (unsigned i = 0; i < e.num_args(); ++i)
                collect_decls_rec(e.arg(i), d);
        }
    }

    PolyDecls collect_decls(const std::vector<expr> &roots)
    {
        PolyDecls d;
        for (const auto &r : roots)
            collect_decls_rec(r, d);
        return d;
    }

    expr mk_decl_app(context &ctx, Z3_func_decl raw, const std::vector<expr> &args)
    {
        if (!raw)
            throw std::runtime_error("missing polynomial constructor declaration");
        func_decl fd(ctx, raw);
        return fd((unsigned)args.size(), args.data());
    }

    expr mk_pconst(const PolyDecls &d, const expr &v)
    {
        return mk_decl_app(v.ctx(), d.pconst, {v});
    }

    expr mk_pconst_mpz(const PolyDecls &d, context &ctx, const mpz_class &v)
    {
        return mk_pconst(d, int_val(ctx, v));
    }

    expr mk_padd(const PolyDecls &d, const expr &a, const expr &b)
    {
        return mk_decl_app(a.ctx(), d.padd, {a, b});
    }

    expr mk_psub(const PolyDecls &d, const expr &a, const expr &b)
    {
        return mk_decl_app(a.ctx(), d.psub, {a, b});
    }

    expr mk_pmul(const PolyDecls &d, const expr &a, const expr &b)
    {
        return mk_decl_app(a.ctx(), d.pmul, {a, b});
    }

    expr mk_ppow(const PolyDecls &d, const expr &a, const expr &k)
    {
        return mk_decl_app(a.ctx(), d.ppow, {a, k});
    }

    expr mk_eqp(const PolyDecls &d, const expr &a, const expr &b)
    {
        return mk_decl_app(a.ctx(), d.eqp, {a, b});
    }

    expr mk_eqmodp1(const PolyDecls &d, const expr &a, const expr &b, const expr &m)
    {
        return mk_decl_app(a.ctx(), d.eqmodp1, {a, b, m});
    }

    bool extract_poly_int_constant(const expr &p, mpz_class &k)
    {
        return is_ctor(p, "PConst", 1) && parse_mpz_numeral(p.arg(0), k);
    }

    std::size_t expr_size(const expr &e)
    {
        std::size_t n = 1;
        if (e.is_app())
            for (unsigned i = 0; i < e.num_args(); ++i)
                n += expr_size(e.arg(i));
        return n;
    }

    bool is_poly_variable(const expr &e)
    {
        if (is_ctor(e, "PVar", 1))
            return true;
        return is_ctor(e, "PConst", 1) && is_int_atom(e.arg(0));
    }

    std::string variable_key(const expr &e)
    {
        if (is_ctor(e, "PVar", 1))
        {
            std::string nm;
            if (get_string_literal_smt(e.arg(0), nm))
                return "PVar:" + nm;
            return "PVar:" + e.to_string();
        }
        if (is_ctor(e, "PConst", 1))
            return "PConst:" + e.arg(0).to_string();
        return "Sub:" + e.to_string();
    }

    void collect_vars_rec(const expr &e, std::unordered_set<std::string> &out)
    {
        if (is_poly_variable(e))
        {
            out.insert(variable_key(e));
            return;
        }
        if (!e.is_app())
            return;
        for (unsigned i = 0; i < e.num_args(); ++i)
            collect_vars_rec(e.arg(i), out);
    }

    std::unordered_set<std::string> collect_vars(const expr &e)
    {
        std::unordered_set<std::string> out;
        collect_vars_rec(e, out);
        return out;
    }

    std::vector<std::string> collect_sorted_vars(const expr &e)
    {
        std::unordered_set<std::string> vars = collect_vars(e);
        std::vector<std::string> out(vars.begin(), vars.end());
        std::sort(out.begin(), out.end());
        return out;
    }

    void collect_vars_vec_rec(const expr &e, std::vector<std::string> &out)
    {
        if (is_poly_variable(e))
        {
            out.push_back(variable_key(e));
            return;
        }
        if (!e.is_app())
            return;
        for (unsigned i = 0; i < e.num_args(); ++i)
            collect_vars_vec_rec(e.arg(i), out);
    }

    bool expr_matches_key(const expr &root, const expr &sub, const std::string &sub_key, bool sub_is_var)
    {
        if (same_ast(root, sub))
            return true;
        if (sub_is_var)
            return is_poly_variable(root) && variable_key(root) == sub_key;
        return expr_key(root) == sub_key;
    }

    bool contains_expr_keyed(const expr &root, const expr &sub, const std::string &sub_key, bool sub_is_var)
    {
        if (expr_matches_key(root, sub, sub_key, sub_is_var))
            return true;
        if (!root.is_app())
            return false;
        for (unsigned i = 0; i < root.num_args(); ++i)
            if (contains_expr_keyed(root.arg(i), sub, sub_key, sub_is_var))
                return true;
        return false;
    }

    bool contains_expr(const expr &root, const expr &sub)
    {
        const bool sub_is_var = is_poly_variable(sub);
        const std::string sub_key = sub_is_var ? variable_key(sub) : expr_key(sub);
        return contains_expr_keyed(root, sub, sub_key, sub_is_var);
    }

    std::size_t occurs_count_keyed(const expr &root, const expr &sub, const std::string &sub_key, bool sub_is_var)
    {
        std::size_t n = expr_matches_key(root, sub, sub_key, sub_is_var) ? 1 : 0;
        if (root.is_app())
            for (unsigned i = 0; i < root.num_args(); ++i)
                n += occurs_count_keyed(root.arg(i), sub, sub_key, sub_is_var);
        return n;
    }

    std::size_t occurs_count(const expr &root, const expr &sub)
    {
        const bool sub_is_var = is_poly_variable(sub);
        const std::string sub_key = sub_is_var ? variable_key(sub) : expr_key(sub);
        return occurs_count_keyed(root, sub, sub_key, sub_is_var);
    }

    bool is_numeric_const(const expr &e, const mpz_class &v)
    {
        mpz_class k;
        return extract_poly_int_constant(e, k) && k == v;
    }

    struct PolySimplifyMemoEntry
    {
        expr original;
        expr simplified;

        PolySimplifyMemoEntry(const expr &o, const expr &s) : original(o), simplified(s) {}
    };

    using SimplifyMemo = std::unordered_map<AstCacheKey, std::vector<PolySimplifyMemoEntry>, AstCacheKeyHash>;
    thread_local SimplifyMemo *active_simplify_memo = nullptr;

    struct ScopedSimplifyMemo
    {
        SimplifyMemo memo;
        SimplifyMemo *previous = nullptr;

        ScopedSimplifyMemo() : previous(active_simplify_memo)
        {
            active_simplify_memo = &memo;
        }

        ~ScopedSimplifyMemo()
        {
            active_simplify_memo = previous;
        }

        ScopedSimplifyMemo(const ScopedSimplifyMemo &) = delete;
        ScopedSimplifyMemo &operator=(const ScopedSimplifyMemo &) = delete;
    };

    expr simplify_poly(const expr &e, const PolyDecls &d);
    expr simplify_poly_impl(const expr &e, const PolyDecls &d);

    expr simplify_pneg(const expr &a, const PolyDecls &d)
    {
        context &ctx = a.ctx();
        mpz_class k;
        if (extract_poly_int_constant(a, k))
            return mk_pconst_mpz(d, ctx, -k);
        if (is_ctor(a, "PNeg", 1))
            return a.arg(0);
        if (is_ctor(a, "PSub", 2))
            return simplify_poly(mk_psub(d, a.arg(1), a.arg(0)), d);
        if (is_ctor(a, "PAdd", 2))
            return simplify_poly(mk_padd(d, simplify_pneg(a.arg(0), d), simplify_pneg(a.arg(1), d)), d);
        return mk_psub(d, mk_pconst_mpz(d, ctx, 0), a);
    }

    expr simplify_poly_cached(const expr &e, const PolyDecls &d, SimplifyMemo &memo)
    {
        if (!e.is_app())
            return e;

        AstCacheKey key{(Z3_context)e.ctx(), ast_id(e)};
        auto it = memo.find(key);
        if (it != memo.end())
        {
            for (const PolySimplifyMemoEntry &entry : it->second)
                if (same_ast(entry.original, e))
                    return entry.simplified;
        }

        expr r = simplify_poly_impl(e, d);
        memo[key].emplace_back(e, r);
        return r;
    }

    expr simplify_poly(const expr &e, const PolyDecls &d)
    {
        if (active_simplify_memo)
            return simplify_poly_cached(e, d, *active_simplify_memo);

        SimplifyMemo memo;
        active_simplify_memo = &memo;
        try
        {
            expr r = simplify_poly_cached(e, d, memo);
            active_simplify_memo = nullptr;
            return r;
        }
        catch (...)
        {
            active_simplify_memo = nullptr;
            throw;
        }
    }

    expr simplify_poly_impl(const expr &e, const PolyDecls &d)
    {
        context &ctx = e.ctx();
        if (!e.is_app())
            return e;

        if (is_ctor(e, "PConst", 1))
            return mk_pconst(d, e.arg(0).simplify());
        if (is_ctor(e, "PVar", 1))
            return e;

        if (is_ctor(e, "PNeg", 1))
            return simplify_pneg(simplify_poly(e.arg(0), d), d);

        if (is_ctor(e, "PAdd", 2) || is_ctor(e, "PSub", 2))
        {
            expr a = simplify_poly(e.arg(0), d);
            expr b = simplify_poly(e.arg(1), d);
            const bool is_add = is_ctor(e, "PAdd", 2);
            mpz_class ka, kb;
            if (is_add)
            {
                if (is_numeric_const(a, 0))
                    return b;
                if (is_numeric_const(b, 0))
                    return a;
                if (extract_poly_int_constant(a, ka) && extract_poly_int_constant(b, kb))
                    return mk_pconst_mpz(d, ctx, ka + kb);
                return mk_padd(d, a, b);
            }

            if (is_numeric_const(b, 0))
                return a;
            if (same_ast(a, b) || expr_key(a) == expr_key(b))
                return mk_pconst_mpz(d, ctx, 0);
            if (is_numeric_const(a, 0))
                return simplify_pneg(b, d);
            if (extract_poly_int_constant(a, ka) && extract_poly_int_constant(b, kb))
                return mk_pconst_mpz(d, ctx, ka - kb);
            if (extract_poly_int_constant(b, kb) && kb < 0)
                return simplify_poly(mk_padd(d, a, mk_pconst_mpz(d, ctx, -kb)), d);
            return mk_psub(d, a, b);
        }

        if (is_ctor(e, "PMul", 2))
        {
            expr a = simplify_poly(e.arg(0), d);
            expr b = simplify_poly(e.arg(1), d);
            mpz_class ka, kb;
            if (is_numeric_const(a, 0) || is_numeric_const(b, 0))
                return mk_pconst_mpz(d, ctx, 0);
            if (is_numeric_const(a, 1))
                return b;
            if (is_numeric_const(b, 1))
                return a;
            if (is_numeric_const(a, -1))
                return simplify_pneg(b, d);
            if (is_numeric_const(b, -1))
                return simplify_pneg(a, d);
            if (extract_poly_int_constant(a, ka) && extract_poly_int_constant(b, kb))
                return mk_pconst_mpz(d, ctx, ka * kb);
            return mk_pmul(d, a, b);
        }

        if (is_ctor(e, "PPow", 2))
        {
            expr a = simplify_poly(e.arg(0), d);
            int64_t k = -1;
            if (get_int64_numeral(e.arg(1), k))
            {
                if (k == 0)
                    return mk_pconst_mpz(d, ctx, 1);
                if (k == 1)
                    return a;
            }
            return mk_ppow(d, a, e.arg(1));
        }

        return e.simplify();
    }

    bool is_zero_poly(const expr &e, const PolyDecls &d)
    {
        expr s = simplify_poly(e, d);
        return is_numeric_const(s, 0);
    }

    struct Affine
    {
        std::map<std::string, mpz_class> coeffs;
        std::map<std::string, expr> var_exprs;
        mpz_class constant = 0;

        explicit Affine(context &) {}
    };

    void affine_add_scaled(Affine &dst, const Affine &src, const mpz_class &scale)
    {
        dst.constant += scale * src.constant;
        for (const auto &kv : src.coeffs)
        {
            dst.coeffs[kv.first] += scale * kv.second;
            if (dst.coeffs[kv.first] == 0)
                dst.coeffs.erase(kv.first);
        }
        for (const auto &kv : src.var_exprs)
            dst.var_exprs.emplace(kv.first, kv.second);
    }

    bool affine_extract_poly(const expr &p, const PolyDecls &d, Affine &out)
    {
        out.coeffs.clear();
        out.var_exprs.clear();
        out.constant = 0;

        mpz_class k;
        if (extract_poly_int_constant(p, k))
        {
            out.constant = k;
            return true;
        }

        if (is_poly_variable(p))
        {
            const std::string key = variable_key(p);
            out.coeffs[key] = 1;
            out.var_exprs.emplace(key, p);
            return true;
        }

        if (is_ctor(p, "PConst", 1))
            return false;

        if (is_ctor(p, "PNeg", 1))
        {
            Affine a(p.ctx());
            if (!affine_extract_poly(p.arg(0), d, a))
                return false;
            affine_add_scaled(out, a, -1);
            return true;
        }

        if (is_ctor(p, "PAdd", 2) || is_ctor(p, "PSub", 2))
        {
            Affine a(p.ctx()), b(p.ctx());
            if (!affine_extract_poly(p.arg(0), d, a) || !affine_extract_poly(p.arg(1), d, b))
                return false;
            affine_add_scaled(out, a, 1);
            affine_add_scaled(out, b, is_ctor(p, "PAdd", 2) ? mpz_class(1) : mpz_class(-1));
            return true;
        }

        if (is_ctor(p, "PMul", 2))
        {
            mpz_class lhs_k, rhs_k;
            if (extract_poly_int_constant(p.arg(0), lhs_k))
            {
                Affine b(p.ctx());
                if (!affine_extract_poly(p.arg(1), d, b))
                    return false;
                affine_add_scaled(out, b, lhs_k);
                return true;
            }
            if (extract_poly_int_constant(p.arg(1), rhs_k))
            {
                Affine a(p.ctx());
                if (!affine_extract_poly(p.arg(0), d, a))
                    return false;
                affine_add_scaled(out, a, rhs_k);
                return true;
            }
            return false;
        }

        if (is_ctor(p, "PPow", 2))
        {
            int64_t k64 = -1;
            if (!get_int64_numeral(p.arg(1), k64))
                return false;
            if (k64 == 0)
            {
                out.constant = 1;
                return true;
            }
            if (k64 == 1)
                return affine_extract_poly(p.arg(0), d, out);
            return false;
        }

        return false;
    }

    bool contains_multiplicative_or_power(const expr &e)
    {
        if (is_ctor(e, "PMul", 2) || is_ctor(e, "PPow", 2))
            return true;
        if (!e.is_app())
            return false;
        for (unsigned i = 0; i < e.num_args(); ++i)
            if (contains_multiplicative_or_power(e.arg(i)))
                return true;
        return false;
    }

    struct Pattern
    {
        RewriteRule rule;
        std::string lhs_key;

        Pattern(const RewriteRule &r, std::string k) : rule(r), lhs_key(std::move(k)) {}
    };

    std::optional<Pattern> make_variable_assignment(const expr &lhs,
                                                    const expr &rhs0,
                                                    const expr &poly,
                                                    const expr &source,
                                                    const PolyDecls &d,
                                                    bool modular,
                                                    const RewriteOptions &options,
                                                    RewriteStats &stats,
                                                    std::vector<std::string> &diagnostics,
                                                    const std::string &label,
                                                    const char *diagnostic_tag)
    {
        if (!is_poly_variable(lhs))
            return std::nullopt;
        const std::string key = variable_key(lhs);
        if (options.suppressed_lhs_keys.count(key))
            return std::nullopt;
        expr rhs = simplify_poly(rhs0, d);
        std::vector<std::string> rhs_dependencies = collect_sorted_vars(rhs);
        if (std::binary_search(rhs_dependencies.begin(), rhs_dependencies.end(), key))
        {
            ++stats.skipped_lhs_occurs_in_rhs;
            diagnostics.push_back(label + ": skipped " + diagnostic_tag + " lhs occurs in rhs");
            return std::nullopt;
        }
        if (options.enable_expression_growth_check &&
            expr_size(rhs) > expr_size(poly) + options.max_expression_growth)
        {
            ++stats.skipped_expression_growth;
            diagnostics.push_back(label + ": skipped " + diagnostic_tag + " expression growth");
            return std::nullopt;
        }
        RewriteRule r(lhs, rhs, source, RewriteRule::Kind::Variable, modular, label);
        r.rhs_dependencies = std::move(rhs_dependencies);
        return Pattern(r, key);
    }

    bool subsumed_by_moduli(const expr &e,
                            const std::vector<expr> &moduli,
                            const PolyDecls &d,
                            const RewriteOptions &options,
                            RewriteStats &stats);

    void collect_additive_variable_candidates(const expr &e, std::vector<expr> &out)
    {
        if (is_poly_variable(e))
        {
            out.push_back(e);
            return;
        }
        if (is_ctor(e, "PNeg", 1))
        {
            collect_additive_variable_candidates(e.arg(0), out);
            return;
        }
        if (is_ctor(e, "PAdd", 2) || is_ctor(e, "PSub", 2))
        {
            collect_additive_variable_candidates(e.arg(0), out);
            collect_additive_variable_candidates(e.arg(1), out);
        }
    }

    expr isolate_additive_variable(const expr &lhs, const expr &e, const expr &pat, const PolyDecls &d)
    {
        if (same_ast(lhs, e) || expr_key(lhs) == expr_key(e))
            return pat;
        if (is_ctor(e, "PNeg", 1) && contains_expr(e.arg(0), lhs))
            return isolate_additive_variable(lhs, e.arg(0), simplify_pneg(pat, d), d);
        if (is_ctor(e, "PAdd", 2) || is_ctor(e, "PSub", 2))
        {
            const bool in1 = contains_expr(e.arg(0), lhs);
            const bool in2 = contains_expr(e.arg(1), lhs);
            if (is_ctor(e, "PAdd", 2) && in1 && !in2)
                return isolate_additive_variable(lhs, e.arg(0), simplify_poly(mk_padd(d, pat, simplify_pneg(e.arg(1), d)), d), d);
            if (is_ctor(e, "PAdd", 2) && !in1 && in2)
                return isolate_additive_variable(lhs, e.arg(1), simplify_poly(mk_padd(d, pat, simplify_pneg(e.arg(0), d)), d), d);
            if (is_ctor(e, "PSub", 2) && in1 && !in2)
                return isolate_additive_variable(lhs, e.arg(0), simplify_poly(mk_padd(d, pat, e.arg(1)), d), d);
            if (is_ctor(e, "PSub", 2) && !in1 && in2)
                return isolate_additive_variable(lhs, e.arg(1), simplify_poly(mk_padd(d, simplify_pneg(pat, d), e.arg(0)), d), d);
        }
        throw std::runtime_error("variable is not add/sub/neg separable");
    }

    std::optional<Pattern> extract_separable_assignment(const expr &poly,
                                                        const expr &source,
                                                        const PolyDecls &d,
                                                        bool modular,
                                                        const RewriteOptions &options,
                                                        RewriteStats &stats,
                                                        std::vector<std::string> &diagnostics,
                                                        const std::string &label)
    {
        std::vector<expr> candidates;
        collect_additive_variable_candidates(poly, candidates);
        std::sort(candidates.begin(), candidates.end(), [](const expr &a, const expr &b)
                  { return variable_key(a) < variable_key(b); });
        candidates.erase(std::unique(candidates.begin(), candidates.end(), [](const expr &a, const expr &b)
                                     { return same_ast(a, b) || expr_key(a) == expr_key(b); }),
                         candidates.end());

        for (const expr &lhs : candidates)
        {
            if (occurs_count(poly, lhs) != 1)
                continue;
            try
            {
                expr zero = mk_pconst_mpz(d, poly.ctx(), 0);
                expr rhs = simplify_poly(isolate_additive_variable(lhs, poly, zero, d), d);
                if (auto pat = make_variable_assignment(lhs, rhs, poly, source, d, modular,
                                                        options, stats, diagnostics, label, "separable"))
                    return pat;
            }
            catch (const std::exception &)
            {
                continue;
            }
        }
        return std::nullopt;
    }

    // Priority path for the instruction-shaped patterns used by rewrite.ml
    // before the general separable fallback tries candidates in sorted order.
    std::optional<Pattern> extract_common_assignment(const expr &poly,
                                                     const expr &source,
                                                     const std::vector<expr> &moduli,
                                                     const PolyDecls &d,
                                                     bool modular,
                                                     const RewriteOptions &options,
                                                     RewriteStats &stats,
                                                     std::vector<std::string> &diagnostics,
                                                     const std::string &label)
    {
        if (!is_ctor(poly, "PSub", 2))
            return std::nullopt;

        const expr a = poly.arg(0);
        const expr b = poly.arg(1);

        if (is_ctor(a, "PSub", 2) && subsumed_by_moduli(b, moduli, d, options, stats))
        {
            const expr inner_l = a.arg(0);
            const expr inner_r = a.arg(1);
            if (is_poly_variable(inner_l) && !contains_expr(b, inner_l))
                return make_variable_assignment(inner_l, inner_r, poly, source, d, true, options, stats,
                                                diagnostics, label, "common");
            if (is_poly_variable(inner_r) && !contains_expr(b, inner_r))
                return make_variable_assignment(inner_r, inner_l, poly, source, d, true, options, stats,
                                                diagnostics, label, "common");
        }

        if (is_poly_variable(a) && !contains_expr(b, a))
            return make_variable_assignment(a, b, poly, source, d, modular, options, stats, diagnostics, label, "common");
        if (is_poly_variable(b) && !contains_expr(a, b))
            return make_variable_assignment(b, a, poly, source, d, modular, options, stats, diagnostics, label, "common");

        if (is_ctor(a, "PAdd", 2))
        {
            const expr add_l = a.arg(0);
            const expr add_r = a.arg(1);
            if (is_poly_variable(add_l) && !contains_expr(add_r, add_l) && !contains_expr(b, add_l))
                return make_variable_assignment(add_l, mk_psub(d, b, add_r), poly, source, d, modular,
                                                options, stats, diagnostics, label, "common");
        }
        if (is_ctor(b, "PAdd", 2))
        {
            const expr add_l = b.arg(0);
            const expr add_r = b.arg(1);
            if (is_poly_variable(add_l) && !contains_expr(add_r, add_l) && !contains_expr(a, add_l))
                return make_variable_assignment(add_l, mk_psub(d, a, add_r), poly, source, d, modular,
                                                options, stats, diagnostics, label, "common");
        }
        return std::nullopt;
    }

    std::optional<Pattern> extract_variable_assignment_pattern(const expr &poly,
                                                               const expr &source,
                                                               const std::vector<expr> &moduli,
                                                               const PolyDecls &d,
                                                               bool modular,
                                                               const RewriteOptions &options,
                                                               RewriteStats &stats,
                                                               std::vector<std::string> &diagnostics,
                                                               const std::string &label)
    {
        if (auto common = extract_common_assignment(poly, source, moduli, d, modular,
                                                    options, stats, diagnostics, label))
            return common;
        if (auto separable = extract_separable_assignment(poly, source, d, modular, options, stats, diagnostics, label))
            return separable;
        return std::nullopt;
    }

    void collect_subexprs_with_vars(const expr &e, std::vector<expr> &out)
    {
        if (!collect_vars(e).empty())
            out.push_back(e);
        if (!e.is_app())
            return;
        if (is_ctor(e, "PVar", 1))
            return;
        for (unsigned i = 0; i < e.num_args(); ++i)
            collect_subexprs_with_vars(e.arg(i), out);
    }

    bool vars_disjoint_except_eq(const expr &sub, const expr &root)
    {
        const std::unordered_set<std::string> vars_sub = collect_vars(sub);
        if (vars_sub.empty())
            return false;

        std::function<bool(const expr &)> rec = [&](const expr &cur) -> bool
        {
            if (same_ast(cur, sub) || expr_key(cur) == expr_key(sub))
                return true;
            if (is_poly_variable(cur))
                return vars_sub.find(variable_key(cur)) == vars_sub.end();
            if (!cur.is_app())
                return true;
            for (unsigned i = 0; i < cur.num_args(); ++i)
                if (!rec(cur.arg(i)))
                    return false;
            return true;
        };
        return rec(root);
    }

    expr separate_subexpr(const expr &sub, const expr &e, const expr &pat, const PolyDecls &d)
    {
        if (same_ast(sub, e) || expr_key(sub) == expr_key(e))
            return pat;
        if (is_ctor(e, "PNeg", 1) && contains_expr(e.arg(0), sub))
            return separate_subexpr(sub, e.arg(0), simplify_pneg(pat, d), d);
        if (is_ctor(e, "PAdd", 2) || is_ctor(e, "PSub", 2))
        {
            const bool in1 = contains_expr(e.arg(0), sub);
            const bool in2 = contains_expr(e.arg(1), sub);
            if (is_ctor(e, "PAdd", 2) && in1 && !in2)
                return separate_subexpr(sub, e.arg(0), simplify_poly(mk_padd(d, pat, simplify_pneg(e.arg(1), d)), d), d);
            if (is_ctor(e, "PAdd", 2) && !in1 && in2)
                return separate_subexpr(sub, e.arg(1), simplify_poly(mk_padd(d, pat, simplify_pneg(e.arg(0), d)), d), d);
            if (is_ctor(e, "PSub", 2) && in1 && !in2)
                return separate_subexpr(sub, e.arg(0), simplify_poly(mk_padd(d, pat, e.arg(1)), d), d);
            if (is_ctor(e, "PSub", 2) && !in1 && in2)
                return separate_subexpr(sub, e.arg(1), simplify_poly(mk_padd(d, simplify_pneg(pat, d), e.arg(0)), d), d);
        }
        throw std::runtime_error("subexpression is not add/sub/neg separable");
    }

    // Corresponds to rewrite.ml:get_rewrite_pattern'. Subexpression rules stay
    // additive-only; nonlinear PMul/PPow subexpressions remain residuals.
    std::optional<Pattern> extract_rewrite_pattern_subexpr(const expr &poly,
                                                           const expr &source,
                                                           const std::vector<expr> &others,
                                                           const PolyDecls &d,
                                                           bool modular,
                                                           const RewriteOptions &options,
                                                           RewriteStats &stats,
                                                           std::vector<std::string> &diagnostics,
                                                           const std::string &label)
    {
        std::vector<expr> subs;
        collect_subexprs_with_vars(poly, subs);
        std::sort(subs.begin(), subs.end(), [](const expr &a, const expr &b)
                  {
                  const std::size_t sa = expr_size(a), sb = expr_size(b);
                  if (sa != sb)
                      return sa < sb;
                  return a.to_string() < b.to_string(); });

        const std::string whole_key = expr_key(poly);
        for (const expr &sub : subs)
        {
            if (expr_key(sub) == whole_key || is_poly_variable(sub))
                continue;
            if (contains_multiplicative_or_power(sub))
                continue;
            if (occurs_count(poly, sub) != 1)
                continue;
            if (!vars_disjoint_except_eq(sub, poly))
                continue;
            bool ok_others = true;
            for (const expr &other : others)
            {
                if (!vars_disjoint_except_eq(sub, other))
                {
                    ok_others = false;
                    break;
                }
            }
            if (!ok_others)
                continue;

            try
            {
                expr zero = mk_pconst_mpz(d, poly.ctx(), 0);
                expr rhs = simplify_poly(separate_subexpr(sub, poly, zero, d), d);
                if (contains_expr(rhs, sub))
                {
                    ++stats.skipped_lhs_occurs_in_rhs;
                    diagnostics.push_back(label + ": skipped subexpression lhs occurs in rhs");
                    continue;
                }
                if (options.enable_expression_growth_check &&
                    expr_size(rhs) > expr_size(poly) + options.max_expression_growth)
                {
                    ++stats.skipped_expression_growth;
                    diagnostics.push_back(label + ": skipped subexpression growth");
                    continue;
                }
                RewriteRule r(sub, rhs, source, RewriteRule::Kind::SubExpression, modular, label);
                r.rhs_dependencies = collect_sorted_vars(rhs);
                return Pattern(r, "Sub:" + sub.to_string());
            }
            catch (const std::exception &)
            {
                continue;
            }
        }
        return std::nullopt;
    }

    bool term_contains_modulus_factor(const expr &term, const std::vector<expr> &moduli)
    {
        for (const expr &m : moduli)
            if (same_ast(term, m) || expr_key(term) == expr_key(m))
                return true;
        if (is_ctor(term, "PMul", 2))
            return term_contains_modulus_factor(term.arg(0), moduli) ||
                   term_contains_modulus_factor(term.arg(1), moduli);
        return false;
    }

    bool structurally_subsumed_by_moduli(const expr &e, const std::vector<expr> &moduli)
    {
        if (moduli.empty())
            return false;
        for (const expr &m : moduli)
            if (same_ast(e, m) || expr_key(e) == expr_key(m))
                return true;
        if (is_ctor(e, "PNeg", 1))
            return structurally_subsumed_by_moduli(e.arg(0), moduli);
        if (is_ctor(e, "PAdd", 2) || is_ctor(e, "PSub", 2))
            return structurally_subsumed_by_moduli(e.arg(0), moduli) &&
                   structurally_subsumed_by_moduli(e.arg(1), moduli);
        return term_contains_modulus_factor(e, moduli);
    }

    struct SingularRing
    {
        ring R = nullptr;
        std::vector<char *> names;
        rRingOrder_t *ord = nullptr;
        int *block0 = nullptr;
        int *block1 = nullptr;
        int ord_size = 0;

        ~SingularRing()
        {
            if (R)
                rDelete(R);
            for (char *p : names)
                free(p);
        }

        void build(const std::vector<std::string> &vars)
        {
            coeffs cfZ = nCopyCoeff(singular_shared_coeffs_Z());

            int nvars = (int)std::max<std::size_t>(1, vars.size());
            names.reserve((std::size_t)nvars);
            if (vars.empty())
                names.push_back(strdup("k"));
            else
                for (const auto &v : vars)
                    names.push_back(strdup(v.c_str()));

            ord_size = 3;
            ord = (rRingOrder_t *)omAlloc(ord_size * sizeof(rRingOrder_t));
            block0 = (int *)omAlloc0(ord_size * sizeof(int));
            block1 = (int *)omAlloc0(ord_size * sizeof(int));
            ord[0] = ringorder_dp;
            ord[1] = ringorder_C;
            ord[2] = (rRingOrder_t)0;
            block0[0] = 1;
            block1[0] = nvars;

            R = rDefault(cfZ, nvars, names.data(), ord_size, ord, block0, block1, nullptr);
            if (!R)
                throw std::runtime_error("Singular rDefault failed");
            rComplete(R);
            rChangeCurrRing(R);
        }
    };

    number singular_num_from_mpz(const mpz_class &v, const coeffs cf)
    {
        mpz_t z;
        mpz_init_set(z, v.get_mpz_t());
        number n = n_InitMPZ(z, cf);
        mpz_clear(z);
        return n;
    }

    poly singular_poly_from_mpz(const mpz_class &v, const ring R)
    {
        return p_NSet(singular_num_from_mpz(v, R->cf), R);
    }

    void collect_singular_var_keys(const expr &e, std::set<std::string> &out)
    {
        if (is_poly_variable(e))
        {
            out.insert(variable_key(e));
            return;
        }
        if (!e.is_app())
            return;
        for (unsigned i = 0; i < e.num_args(); ++i)
            collect_singular_var_keys(e.arg(i), out);
    }

    poly singular_var_poly(const std::string &key,
                           const std::unordered_map<std::string, int> &idx,
                           const ring R)
    {
        auto it = idx.find(key);
        if (it == idx.end())
            throw std::runtime_error("Singular variable missing: " + key);
        poly p = p_NSet(singular_num_from_mpz(1, R->cf), R);
        p_SetExp(p, it->second, 1, R);
        p_Setm(p, R);
        return p;
    }

    poly singular_from_poly_expr(const expr &e,
                                 const PolyDecls &d,
                                 const std::unordered_map<std::string, int> &idx,
                                 const ring R)
    {
        (void)d;
        rChangeCurrRing(R);
        mpz_class k;
        if (extract_poly_int_constant(e, k))
            return singular_poly_from_mpz(k, R);
        if (is_poly_variable(e))
            return singular_var_poly(variable_key(e), idx, R);
        if (is_ctor(e, "PNeg", 1))
        {
            poly a = singular_from_poly_expr(e.arg(0), d, idx, R);
            number m1 = singular_num_from_mpz(-1, R->cf);
            poly r = p_Mult_nn(a, m1, R);
            n_Delete(&m1, R->cf);
            return r;
        }
        if (is_ctor(e, "PAdd", 2))
        {
            poly a = singular_from_poly_expr(e.arg(0), d, idx, R);
            poly b = singular_from_poly_expr(e.arg(1), d, idx, R);
            return p_Add_q(a, b, R);
        }
        if (is_ctor(e, "PSub", 2))
        {
            poly a = singular_from_poly_expr(e.arg(0), d, idx, R);
            poly b = singular_from_poly_expr(e.arg(1), d, idx, R);
            number m1 = singular_num_from_mpz(-1, R->cf);
            poly bn = p_Mult_nn(b, m1, R);
            n_Delete(&m1, R->cf);
            return p_Add_q(a, bn, R);
        }
        if (is_ctor(e, "PMul", 2))
        {
            poly a = singular_from_poly_expr(e.arg(0), d, idx, R);
            poly b = singular_from_poly_expr(e.arg(1), d, idx, R);
            return p_Mult_q(a, b, R);
        }
        if (is_ctor(e, "PPow", 2))
        {
            int64_t exp = -1;
            if (!get_int64_numeral(e.arg(1), exp) || exp < 0 || exp > 64)
                throw std::runtime_error("unsupported PPow exponent for rewrite normalization");
            poly acc = singular_poly_from_mpz(1, R);
            for (int64_t i = 0; i < exp; ++i)
            {
                poly base = singular_from_poly_expr(e.arg(0), d, idx, R);
                acc = p_Mult_q(acc, base, R);
            }
            return acc;
        }
        throw std::runtime_error("unsupported polynomial expression for Singular: " + e.to_string());
    }

    bool singular_reduces_to_zero(const expr &p,
                                  const std::vector<expr> &moduli,
                                  const PolyDecls &d,
                                  RewriteStats &stats)
    {
        ++stats.singular_nf_checks;
        try
        {
            std::set<std::string> keys;
            collect_singular_var_keys(p, keys);
            for (const expr &m : moduli)
                collect_singular_var_keys(m, keys);

            std::vector<std::string> ring_vars;
            std::unordered_map<std::string, int> idx;
            int n = 1;
            for (const std::string &k : keys)
            {
                ring_vars.push_back("v" + std::to_string(n));
                idx[k] = n;
                ++n;
            }

            SingularRing sr;
            sr.build(ring_vars);
            ring R = sr.R;
            rChangeCurrRing(R);

            if (moduli.empty())
            {
                poly pp = singular_from_poly_expr(p, d, idx, R);
                const bool zero = (pp == nullptr);
                if (pp)
                    p_Delete(&pp, R);
                if (zero)
                    ++stats.singular_zero_reductions;
                return zero;
            }

            ideal I = idInit((int)moduli.size(), 1);
            for (int i = 0; i < (int)moduli.size(); ++i)
                I->m[i] = singular_from_poly_expr(moduli[(std::size_t)i], d, idx, R);
            intvec *w0 = nullptr;
            intvec **w = &w0;
            ideal G = kStd(I, NULL, testHomog, w, NULL, 0, 0, NULL);
            poly pp = singular_from_poly_expr(p, d, idx, R);
            poly nf = kNF(G, NULL, pp, 0, 0);
            const bool zero = (nf == nullptr);
            if (nf)
                p_Delete(&nf, R);
            if (zero)
                ++stats.singular_zero_reductions;
            return zero;
        }
        catch (const std::exception &)
        {
            ++stats.singular_failures;
            return false;
        }
    }

    bool poly_equiv_zero(const expr &p,
                         const std::vector<expr> &moduli,
                         const PolyDecls &d,
                         const RewriteOptions &options,
                         RewriteStats &stats)
    {
        if (is_zero_poly(p, d))
            return true;
        Affine a(p.ctx());
        if (affine_extract_poly(p, d, a) && a.coeffs.empty() && a.constant == 0)
            return true;
        if (options.use_singular_normalization)
            return singular_reduces_to_zero(simplify_poly(p, d), moduli, d, stats);
        return false;
    }

    bool equivalent_poly(const expr &a,
                         const expr &b,
                         const std::vector<expr> &moduli,
                         const PolyDecls &d,
                         const RewriteOptions &options,
                         RewriteStats &stats)
    {
        if (same_ast(a, b) || expr_key(a) == expr_key(b))
            return true;
        return poly_equiv_zero(simplify_poly(mk_psub(d, a, b), d), moduli, d, options, stats);
    }

    bool subsumed_by_moduli(const expr &e,
                            const std::vector<expr> &moduli,
                            const PolyDecls &d,
                            const RewriteOptions &options,
                            RewriteStats &stats)
    {
        if (moduli.empty())
            return false;
        if (structurally_subsumed_by_moduli(e, moduli))
            return true;
        if (options.use_singular_normalization)
            return singular_reduces_to_zero(e, moduli, d, stats);
        return false;
    }

    bool affine_scalar_multiple_of(const expr &p, const expr &modulus, const PolyDecls &d)
    {
        Affine ap(p.ctx()), am(p.ctx());
        if (!affine_extract_poly(p, d, ap) || !affine_extract_poly(modulus, d, am))
            return false;
        if (am.coeffs.empty() && am.constant == 0)
            return false;

        mpz_class numerator;
        mpz_class denominator;
        bool have_ratio = false;
        auto take_ratio = [&](const mpz_class &pv, const mpz_class &mv) -> bool
        {
            if (mv == 0)
                return pv == 0;
            if (!have_ratio)
            {
                numerator = pv;
                denominator = mv;
                have_ratio = true;
                return true;
            }
            return pv * denominator == numerator * mv;
        };

        std::set<std::string> keys;
        for (const auto &kv : ap.coeffs)
            keys.insert(kv.first);
        for (const auto &kv : am.coeffs)
            keys.insert(kv.first);

        for (const std::string &key : keys)
        {
            mpz_class pv = 0;
            mpz_class mv = 0;
            if (auto it = ap.coeffs.find(key); it != ap.coeffs.end())
                pv = it->second;
            if (auto it = am.coeffs.find(key); it != am.coeffs.end())
                mv = it->second;
            if (!take_ratio(pv, mv))
                return false;
        }
        if (!take_ratio(ap.constant, am.constant))
            return false;
        if (!have_ratio)
            return false;
        return numerator % denominator == 0;
    }

    bool affine_multiple_of_any_modulus(const expr &p, const std::vector<expr> &moduli, const PolyDecls &d)
    {
        for (const expr &m : moduli)
            if (affine_scalar_multiple_of(p, m, d))
                return true;
        return false;
    }

    expr finish_moduli_normalized(const expr &e,
                                  const std::vector<expr> &moduli,
                                  const PolyDecls &d)
    {
        expr s = simplify_poly(e, d);
        if (moduli.empty() || !is_poly_ctor(s))
            return s;

        context &ctx = s.ctx();
        if (structurally_subsumed_by_moduli(s, moduli) || affine_multiple_of_any_modulus(s, moduli, d))
            return mk_pconst_mpz(d, ctx, 0);
        return s;
    }

    expr normalize_poly_under_moduli(const expr &e,
                                     const std::vector<expr> &moduli,
                                     const PolyDecls &d,
                                     const RewriteOptions &options,
                                     RewriteStats &stats)
    {
        expr s = is_poly_ctor(e) ? simplify_poly(e, d) : e.simplify();
        if (moduli.empty() || !is_poly_ctor(s))
            return s;

        context &ctx = s.ctx();
        if (structurally_subsumed_by_moduli(s, moduli) || affine_multiple_of_any_modulus(s, moduli, d))
            return mk_pconst_mpz(d, ctx, 0);

        if (is_ctor(s, "PNeg", 1))
            return finish_moduli_normalized(simplify_pneg(normalize_poly_under_moduli(s.arg(0), moduli, d, options, stats), d),
                                            moduli, d);

        if (is_ctor(s, "PAdd", 2))
        {
            expr a = normalize_poly_under_moduli(s.arg(0), moduli, d, options, stats);
            expr b = normalize_poly_under_moduli(s.arg(1), moduli, d, options, stats);
            return finish_moduli_normalized(mk_padd(d, a, b), moduli, d);
        }

        if (is_ctor(s, "PSub", 2))
        {
            expr a = normalize_poly_under_moduli(s.arg(0), moduli, d, options, stats);
            expr b = normalize_poly_under_moduli(s.arg(1), moduli, d, options, stats);
            return finish_moduli_normalized(mk_psub(d, a, b), moduli, d);
        }

        if (is_ctor(s, "PMul", 2))
        {
            expr a = normalize_poly_under_moduli(s.arg(0), moduli, d, options, stats);
            expr b = normalize_poly_under_moduli(s.arg(1), moduli, d, options, stats);
            expr r = simplify_poly(mk_pmul(d, a, b), d);
            if (structurally_subsumed_by_moduli(r, moduli) || affine_multiple_of_any_modulus(r, moduli, d))
                return mk_pconst_mpz(d, ctx, 0);
            return finish_moduli_normalized(r, moduli, d);
        }

        if (is_ctor(s, "PPow", 2))
        {
            expr base = normalize_poly_under_moduli(s.arg(0), moduli, d, options, stats);
            int64_t k = -1;
            if (is_zero_poly(base, d) && get_int64_numeral(s.arg(1), k) && k > 0)
                return mk_pconst_mpz(d, ctx, 0);
            expr r = simplify_poly(mk_ppow(d, base, s.arg(1)), d);
            if (structurally_subsumed_by_moduli(r, moduli) || affine_multiple_of_any_modulus(r, moduli, d))
                return mk_pconst_mpz(d, ctx, 0);
            return finish_moduli_normalized(r, moduli, d);
        }
        return s;
    }

    struct GeneratorInfo
    {
        expr residual;
        expr polynomial;
        bool modular = false;
        bool usable = true;
        std::string label;

        GeneratorInfo(const expr &r, const expr &p, bool m, bool u, std::string l)
            : residual(r), polynomial(p), modular(m), usable(u), label(std::move(l))
        {
        }
    };

    std::optional<GeneratorInfo> generator_to_polynomial(const expr &g,
                                                         const std::vector<expr> &moduli,
                                                         const PolyDecls &d,
                                                         const RewriteOptions &options,
                                                         RewriteStats &stats,
                                                         std::vector<std::string> &diagnostics,
                                                         const std::string &label)
    {
        if (g.is_app() && g.decl().name().str() == "eqP" && g.num_args() == 2)
        {
            expr p = simplify_poly(mk_psub(d, g.arg(0), g.arg(1)), d);
            p = normalize_poly_under_moduli(p, moduli, d, options, stats);
            return GeneratorInfo(p, p, false, true, label);
        }
        if (g.is_app() && g.decl().name().str() == "eqmodP1" && g.num_args() == 3)
        {
            if (!subsumed_by_moduli(g.arg(2), moduli, d, options, stats))
            {
                ++stats.skipped_modulus_not_subsumed;
                diagnostics.push_back(label + ": skipped modulus not subsumed");
                return GeneratorInfo(g, g, true, false, label);
            }
            expr p = simplify_poly(mk_psub(d, g.arg(0), g.arg(1)), d);
            p = normalize_poly_under_moduli(p, moduli, d, options, stats);
            return GeneratorInfo(p, p, true, true, label);
        }
        if (is_poly_ctor(g))
        {
            expr p = normalize_poly_under_moduli(g, moduli, d, options, stats);
            return GeneratorInfo(g, p, false, true, label);
        }
        return std::nullopt;
    }

    std::optional<Pattern> extract_one_assignment(const GeneratorInfo &info,
                                                  const std::vector<expr> &others,
                                                  const std::vector<expr> &moduli,
                                                  const PolyDecls &d,
                                                  const RewriteOptions &options,
                                                  RewriteStats &stats,
                                                  std::vector<std::string> &diagnostics)
    {
        if (!info.usable)
            return std::nullopt;
        auto pat = extract_variable_assignment_pattern(info.polynomial, info.residual, moduli, d,
                                                       info.modular, options, stats, diagnostics,
                                                       info.label);
        if (pat)
            return pat;
        if (options.use_subexpression_rules)
            return extract_rewrite_pattern_subexpr(info.polynomial, info.residual, others, d,
                                                   info.modular, options, stats, diagnostics,
                                                   info.label);
        return std::nullopt;
    }

    struct Extraction
    {
        std::vector<RewriteRule> rules;
        std::vector<expr> residuals;
    };

    Extraction extract_assignments_under_moduli(const std::vector<expr> &generators,
                                                const std::vector<expr> &moduli,
                                                const PolyDecls &d,
                                                const RewriteOptions &options,
                                                RewriteStats &stats,
                                                std::vector<std::string> &diagnostics,
                                                const std::string &trace_scope)
    {
        const std::string scope_prefix = trace_scope.empty() ? "" : trace_scope + "/";

        std::vector<GeneratorInfo> infos;
        infos.reserve(generators.size());
        for (std::size_t i = 0; i < generators.size(); ++i)
        {
            const std::string glabel = scope_prefix + "gen#" + std::to_string(i);
            auto info = generator_to_polynomial(generators[i], moduli, d, options, stats, diagnostics,
                                                glabel);
            if (info)
                infos.push_back(*info);
            else
                diagnostics.push_back(glabel + ": unsupported generator");
        }

        struct Candidate
        {
            Pattern pattern;
            std::size_t index;
            Candidate(const Pattern &p, std::size_t i) : pattern(p), index(i) {}
        };

        std::unordered_map<std::string, std::vector<Candidate>> grouped;
        std::vector<bool> has_candidate(infos.size(), false);
        const std::vector<expr> empty_others;
        for (std::size_t i = 0; i < infos.size(); ++i)
        {
            std::vector<expr> others;
            const std::vector<expr> *others_ref = &empty_others;
            if (options.use_subexpression_rules)
            {
                others.reserve(infos.size() > 0 ? infos.size() - 1 : 0);
                for (std::size_t j = 0; j < infos.size(); ++j)
                    if (i != j)
                        others.push_back(infos[j].polynomial);
                others_ref = &others;
            }

            auto pat = extract_one_assignment(infos[i], *others_ref, moduli, d, options, stats, diagnostics);
            if (pat)
            {
                grouped[pat->lhs_key].emplace_back(*pat, i);
                has_candidate[i] = true;
            }
        }

        Extraction out;
        std::vector<bool> consumed(infos.size(), false);
        for (auto &kv : grouped)
        {
            auto &cands = kv.second;
            const bool has_duplicate_lhs = cands.size() > 1;
            if (has_duplicate_lhs && options.reject_duplicate_lhs)
                stats.duplicate_lhs += cands.size() - 1;

            bool conflict = false;
            if (has_duplicate_lhs && options.reject_conflicting_lhs)
            {
                for (std::size_t i = 1; i < cands.size(); ++i)
                {
                    if (!equivalent_poly(cands[0].pattern.rule.rhs, cands[i].pattern.rule.rhs,
                                         moduli, d, options, stats))
                    {
                        conflict = true;
                        break;
                    }
                }
            }
            if (conflict)
            {
                ++stats.conflicting_lhs;
                diagnostics.push_back("duplicate lhs conflict: " + pretty_rewrite_atom_name(kv.first));
                for (const Candidate &c : cands)
                    consumed[c.index] = false;
                continue;
            }
            if (has_duplicate_lhs && options.reject_duplicate_lhs)
            {
                diagnostics.push_back("duplicate lhs: " + pretty_rewrite_atom_name(kv.first));
                for (const Candidate &c : cands)
                    consumed[c.index] = false;
                continue;
            }

            out.rules.push_back(cands[0].pattern.rule);
            ++stats.rules_extracted;
            consumed[cands[0].index] = true;
        }

        std::sort(out.rules.begin(), out.rules.end(),
                  [](const RewriteRule &a, const RewriteRule &b)
                  {
                      return variable_key(a.lhs) < variable_key(b.lhs);
                  });

        for (std::size_t i = 0; i < infos.size(); ++i)
        {
            if (!has_candidate[i] || !consumed[i])
                out.residuals.push_back(infos[i].polynomial);
        }
        return out;
    }

    bool poly_to_int_expr(const expr &p, const PolyDecls &d, expr &out)
    {
        (void)d;
        context &ctx = p.ctx();
        if (is_ctor(p, "PConst", 1))
        {
            out = p.arg(0).simplify();
            return true;
        }
        if (is_ctor(p, "PNeg", 1))
        {
            expr a(ctx);
            if (!poly_to_int_expr(p.arg(0), d, a))
                return false;
            out = (-a).simplify();
            return true;
        }
        if (is_ctor(p, "PAdd", 2) || is_ctor(p, "PSub", 2) || is_ctor(p, "PMul", 2))
        {
            expr a(ctx), b(ctx);
            if (!poly_to_int_expr(p.arg(0), d, a) || !poly_to_int_expr(p.arg(1), d, b))
                return false;
            if (is_ctor(p, "PAdd", 2))
                out = (a + b).simplify();
            else if (is_ctor(p, "PSub", 2))
                out = (a - b).simplify();
            else
                out = (a * b).simplify();
            return true;
        }
        if (is_ctor(p, "PPow", 2))
        {
            expr a(ctx);
            int64_t k = -1;
            if (!poly_to_int_expr(p.arg(0), d, a) || !get_int64_numeral(p.arg(1), k) || k < 0 || k > 64)
                return false;
            expr acc = ctx.int_val(1);
            for (int64_t i = 0; i < k; ++i)
                acc = (acc * a).simplify();
            out = acc;
            return true;
        }
        return false;
    }

    expr rebuild_app(const expr &e, const std::vector<expr> &args)
    {
        if (!e.is_app())
            return e;
        func_decl fd = e.decl();
        return fd((unsigned)args.size(), args.data());
    }

    bool rule_lhs_matches(const expr &e, const RewriteRule &r, const std::string &lhs_key)
    {
        if (same_ast(e, r.lhs))
            return true;
        if (is_poly_variable(r.lhs))
            return is_poly_variable(e) && variable_key(e) == lhs_key;
        return expr_key(e) == lhs_key;
    }

    expr substitute_one_rec_keyed(const expr &e,
                                  const RewriteRule &r,
                                  const PolyDecls &d,
                                  const std::string &lhs_key,
                                  bool &changed)
    {
        if (rule_lhs_matches(e, r, lhs_key))
        {
            changed = true;
            return r.rhs;
        }
        // if (is_ctor(r.lhs, "PConst", 1) && is_int_atom(r.lhs.arg(0)) &&
        //     e.get_sort().is_int() && (same_ast(e, r.lhs.arg(0)) || expr_key(e) == expr_key(r.lhs.arg(0))))
        // {
        //     expr rhs_int(e.ctx());
        //     if (poly_to_int_expr(r.rhs, d, rhs_int))
        //     {
        //         changed = true;
        //         return rhs_int;
        //     }
        // }

        if (!e.is_app())
            return e;

        std::vector<expr> args;
        args.reserve(e.num_args());
        bool any = false;
        for (unsigned i = 0; i < e.num_args(); ++i)
        {
            bool child_changed = false;
            expr child = substitute_one_rec_keyed(e.arg(i), r, d, lhs_key, child_changed);
            any = any || child_changed;
            args.push_back(child);
        }
        if (!any)
            return e;
        changed = true;
        return rebuild_app(e, args).simplify();
    }

    expr substitute_one_rec(const expr &e, const RewriteRule &r, const PolyDecls &d, bool &changed)
    {
        const std::string lhs_key = is_poly_variable(r.lhs) ? variable_key(r.lhs) : expr_key(r.lhs);
        return substitute_one_rec_keyed(e, r, d, lhs_key, changed);
    }

    expr apply_rules_sequential(const expr &e, const std::vector<RewriteRule> &rules, const PolyDecls &d)
    {
        expr cur = e;
        for (const RewriteRule &r : rules)
        {
            bool changed = false;
            cur = substitute_one_rec(cur, r, d, changed);
            if (changed && is_poly_ctor(cur))
                cur = simplify_poly(cur, d);
            else if (changed)
                cur = cur.simplify();
        }
        return cur;
    }

    struct RewriteMemoEntry
    {
        expr original;
        expr rewritten;
        bool changed = false;

        RewriteMemoEntry(const expr &o, const expr &r, bool c) : original(o), rewritten(r), changed(c) {}
    };

    struct RewriteEnv
    {
        const std::vector<RewriteRule> &rules;
        const PolyDecls &d;
        bool all_variable_rules = true;
        std::unordered_map<std::string, const RewriteRule *> by_lhs;
        std::unordered_map<std::string, expr> expanded;
        std::unordered_map<unsigned, std::vector<RewriteMemoEntry>> memo;
        std::unordered_set<std::string> active;

        RewriteEnv(const std::vector<RewriteRule> &rules_, const PolyDecls &d_)
            : rules(rules_), d(d_)
        {
            for (const RewriteRule &r : rules)
            {
                if (r.kind != RewriteRule::Kind::Variable || !is_poly_variable(r.lhs))
                {
                    all_variable_rules = false;
                    break;
                }
            }

            if (all_variable_rules)
            {
                by_lhs.reserve(rules.size());
                expanded.reserve(rules.size());
                for (const RewriteRule &r : rules)
                    by_lhs.emplace(variable_key(r.lhs), &r);
            }
        }
    };

    expr apply_variable_env_rec(const expr &e, RewriteEnv &env, bool &changed);

    expr expand_variable_rule_env(const std::string &key, RewriteEnv &env)
    {
        auto cached = env.expanded.find(key);
        if (cached != env.expanded.end())
            return cached->second;

        auto it = env.by_lhs.find(key);
        if (it == env.by_lhs.end())
            throw std::runtime_error("missing variable rewrite rule");
        if (!env.active.insert(key).second)
            return it->second->rhs;

        bool rhs_changed = false;
        expr rhs = apply_variable_env_rec(it->second->rhs, env, rhs_changed);
        env.active.erase(key);
        if (rhs_changed && is_poly_ctor(rhs))
            rhs = simplify_poly(rhs, env.d);
        else if (rhs_changed)
            rhs = rhs.simplify();

        auto [pos, _] = env.expanded.emplace(key, rhs);
        return pos->second;
    }

    expr apply_variable_env_rec(const expr &e, RewriteEnv &env, bool &changed)
    {
        const unsigned id = ast_id(e);
        auto cached = env.memo.find(id);
        if (cached != env.memo.end())
        {
            for (const RewriteMemoEntry &entry : cached->second)
            {
                if (same_ast(entry.original, e))
                {
                    changed = entry.changed;
                    return entry.rewritten;
                }
            }
        }

        if (is_poly_variable(e))
        {
            const std::string key = variable_key(e);
            auto it = env.by_lhs.find(key);
            if (it != env.by_lhs.end())
            {
                changed = true;
                expr r = expand_variable_rule_env(key, env);
                if (env.active.find(key) == env.active.end())
                    env.memo[id].emplace_back(e, r, true);
                return r;
            }
        }
        if (!e.is_app())
        {
            changed = false;
            env.memo[id].emplace_back(e, e, false);
            return e;
        }

        std::vector<expr> args;
        args.reserve(e.num_args());
        bool any = false;
        for (unsigned i = 0; i < e.num_args(); ++i)
        {
            bool child_changed = false;
            expr child = apply_variable_env_rec(e.arg(i), env, child_changed);
            any = any || child_changed;
            args.push_back(child);
        }
        if (!any)
        {
            changed = false;
            env.memo[id].emplace_back(e, e, false);
            return e;
        }

        changed = true;
        expr r = rebuild_app(e, args).simplify();
        env.memo[id].emplace_back(e, r, true);
        return r;
    }

    expr apply_rules_with_env(const expr &e, RewriteEnv &env)
    {
        if (env.rules.empty())
            return e;
        if (!env.all_variable_rules)
            return apply_rules_sequential(e, env.rules, env.d);

        bool changed = false;
        expr cur = apply_variable_env_rec(e, env, changed);
        if (changed && is_poly_ctor(cur))
            return simplify_poly(cur, env.d);
        if (changed)
            return cur.simplify();
        return cur;
    }

    expr apply_rules(const expr &e, const std::vector<RewriteRule> &rules, const PolyDecls &d)
    {
        if (rules.empty())
            return e;

        RewriteEnv env(rules, d);
        return apply_rules_with_env(e, env);
    }

    std::vector<std::size_t> topo_sort_rules(const std::vector<RewriteRule> &rules)
    {
        const std::size_t n = rules.size();
        std::unordered_map<std::string, std::size_t> index;
        bool use_dependency_keys = true;
        for (std::size_t i = 0; i < n; ++i)
        {
            if (rules[i].kind != RewriteRule::Kind::Variable || !is_poly_variable(rules[i].lhs))
                use_dependency_keys = false;
            index[variable_key(rules[i].lhs)] = i;
        }

        std::vector<std::vector<std::size_t>> deps(n);
        if (use_dependency_keys)
        {
            for (std::size_t i = 0; i < n; ++i)
            {
                for (const std::string &dep_key : rules[i].rhs_dependencies)
                {
                    auto it = index.find(dep_key);
                    if (it != index.end() && it->second != i)
                        deps[i].push_back(it->second);
                }
                std::sort(deps[i].begin(), deps[i].end());
                deps[i].erase(std::unique(deps[i].begin(), deps[i].end()), deps[i].end());
            }
        }
        else
        {
            for (std::size_t i = 0; i < n; ++i)
            {
                for (std::size_t j = 0; j < n; ++j)
                {
                    if (i != j && contains_expr(rules[i].rhs, rules[j].lhs))
                        deps[i].push_back(j);
                }
                std::sort(deps[i].begin(), deps[i].end());
            }
        }

        std::vector<int> state(n, 0);
        std::vector<std::size_t> sorted;
        std::function<void(std::size_t)> dfs = [&](std::size_t i)
        {
            if (state[i] == 1)
                throw CircularDependency();
            if (state[i] == 2)
                return;
            state[i] = 1;
            for (std::size_t dep : deps[i])
                dfs(dep);
            state[i] = 2;
            sorted.push_back(i);
        };

        std::vector<std::size_t> order(n);
        for (std::size_t i = 0; i < n; ++i)
            order[i] = i;
        std::sort(order.begin(), order.end(), [&](std::size_t a, std::size_t b)
                  { return variable_key(rules[a].lhs) < variable_key(rules[b].lhs); });
        for (std::size_t i : order)
            dfs(i);
        return sorted;
    }

    std::vector<RewriteRule> compose_rules(const std::vector<RewriteRule> &rules,
                                           const std::vector<std::size_t> &sorted,
                                           const PolyDecls &d)
    {
        std::vector<RewriteRule> env;
        env.reserve(rules.size());
        for (std::size_t idx : sorted)
        {
            const RewriteRule &src = rules[idx];
            expr rhs = simplify_poly(apply_rules(src.rhs, env, d), d);
            if (contains_expr(rhs, src.lhs))
                throw CircularDependency();
            RewriteRule r(src.lhs, rhs, src.source_generator, src.kind, src.is_modular, src.source_label);
            r.rhs_dependencies = collect_sorted_vars(rhs);
            env.push_back(r);
        }
        return env;
    }

    std::vector<expr> normalize_residuals(const std::vector<expr> &residuals,
                                          const std::vector<expr> &moduli,
                                          const PolyDecls &d,
                                          const RewriteOptions &options,
                                          RewriteStats &stats)
    {
        std::vector<expr> out;
        std::unordered_set<std::string> seen;
        for (const expr &r0 : residuals)
        {
            expr r = normalize_poly_under_moduli(r0, moduli, d, options, stats);
            if (is_poly_ctor(r) && poly_equiv_zero(r, moduli, d, options, stats))
                continue;
            if (seen.insert(r.to_string()).second)
                out.push_back(r);
        }
        return out;
    }

    RewriteResult try_dag_rewrite(const std::vector<expr> &ideal,
                                  const expr &target,
                                  const std::vector<expr> &moduli,
                                  const PolyDecls &d,
                                  const RewriteOptions &options)
    {
        RewriteResult res(target);
        std::vector<expr> current = ideal;
        expr current_target = target;

        for (std::size_t round = 0; round < options.max_rounds; ++round)
        {
            Extraction ex = extract_assignments_under_moduli(current, moduli, d, options,
                                                             res.stats, res.diagnostics,
                                                             "dag-r" + std::to_string(round));
            if (ex.rules.empty())
            {
                current = normalize_residuals(current, moduli, d, options, res.stats);
                break;
            }

            std::vector<std::size_t> sorted = topo_sort_rules(ex.rules);
            std::vector<RewriteRule> env = compose_rules(ex.rules, sorted, d);
            RewriteEnv rewrite_env(env, d);
            ++res.dag_rounds;
            res.rules_used.insert(res.rules_used.end(), env.begin(), env.end());

            std::vector<expr> rewritten_residuals;
            rewritten_residuals.reserve(ex.residuals.size());
            for (const expr &r : ex.residuals)
                rewritten_residuals.push_back(normalize_poly_under_moduli(apply_rules_with_env(r, rewrite_env),
                                                                          moduli, d, options, res.stats));
            current = normalize_residuals(rewritten_residuals, moduli, d, options, res.stats);
            current_target = normalize_poly_under_moduli(apply_rules_with_env(current_target, rewrite_env),
                                                         moduli, d, options, res.stats);
        }

        res.residual_generators = std::move(current);
        res.rewritten_target = normalize_poly_under_moduli(current_target, moduli, d, options, res.stats);
        return res;
    }

    RewriteResult functional_worklist_rewrite(const std::vector<expr> &ideal,
                                              const expr &target,
                                              const std::vector<expr> &moduli,
                                              const PolyDecls &d,
                                              const RewriteOptions &options)
    {
        RewriteResult res(target);
        res.used_worklist_fallback = true;

        std::deque<expr> stack;
        for (const expr &g : ideal)
            stack.push_back(g);
        std::vector<expr> residuals;
        std::vector<RewriteRule> env;
        std::unordered_map<std::string, std::size_t> env_index;

        std::size_t iterations = 0;
        while (!stack.empty() && iterations++ < options.max_rounds * std::max<std::size_t>(1, ideal.size() + 1))
        {
            expr poly = stack.front();
            stack.pop_front();
            poly = normalize_poly_under_moduli(apply_rules(poly, env, d), moduli, d, options, res.stats);

            auto info = generator_to_polynomial(poly, moduli, d, options, res.stats, res.diagnostics,
                                                "wl-i" + std::to_string(iterations));
            if (!info)
            {
                residuals.push_back(poly);
                continue;
            }
            std::vector<expr> others;
            for (const expr &r : residuals)
                others.push_back(r);
            auto pat = extract_one_assignment(*info, others, moduli, d, options, res.stats, res.diagnostics);
            if (!pat || contains_expr(pat->rule.rhs, pat->rule.lhs))
            {
                residuals.push_back(info->polynomial);
                continue;
            }

            auto existing = env_index.find(pat->lhs_key);
            if (existing != env_index.end())
            {
                bool conflict = false;
                if (options.reject_conflicting_lhs)
                {
                    conflict = !equivalent_poly(env[existing->second].rhs, pat->rule.rhs,
                                                moduli, d, options, res.stats);
                }
                if (conflict)
                {
                    ++res.stats.conflicting_lhs;
                    res.diagnostics.push_back("duplicate lhs conflict: " + pretty_rewrite_atom_name(pat->lhs_key));
                    residuals.push_back(info->polynomial);
                    continue;
                }
                if (options.reject_duplicate_lhs)
                {
                    ++res.stats.duplicate_lhs;
                    res.diagnostics.push_back("duplicate lhs: " + pretty_rewrite_atom_name(pat->lhs_key));
                    residuals.push_back(info->polynomial);
                    continue;
                }
                residuals.push_back(info->polynomial);
                continue;
            }

            RewriteRule new_rule = pat->rule;
            for (RewriteRule &old : env)
            {
                bool changed = false;
                old.rhs = simplify_poly(substitute_one_rec(old.rhs, new_rule, d, changed), d);
            }
            env_index[pat->lhs_key] = env.size();
            env.push_back(new_rule);
            res.rules_used.push_back(new_rule);

            std::vector<expr> keep;
            for (const expr &r : residuals)
            {
                if (contains_expr(r, new_rule.lhs))
                    stack.push_back(r);
                else
                    keep.push_back(r);
            }
            residuals.swap(keep);
        }

        res.rules_used = env;

        std::vector<expr> final_residuals;
        RewriteEnv final_env(env, d);
        for (const expr &r : residuals)
            final_residuals.push_back(normalize_poly_under_moduli(apply_rules_with_env(r, final_env),
                                                                  moduli, d, options, res.stats));
        while (!stack.empty())
        {
            final_residuals.push_back(normalize_poly_under_moduli(apply_rules_with_env(stack.front(), final_env),
                                                                  moduli, d, options, res.stats));
            stack.pop_front();
        }
        res.residual_generators = normalize_residuals(final_residuals, moduli, d, options, res.stats);
        res.rewritten_target = normalize_poly_under_moduli(apply_rules_with_env(target, final_env),
                                                           moduli, d, options, res.stats);
        return res;
    }

    void collect_eqP_rec(const expr &e, std::vector<expr> &atoms)
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

    bool is_eqP_atom(const expr &e)
    {
        return e.is_app() && e.decl().name().str() == "eqP" && e.num_args() == 2;
    }

    void collect_asserted_eqP_rec(const expr &e, std::vector<expr> &atoms)
    {
        if (is_eqP_atom(e))
        {
            atoms.push_back(e);
            return;
        }
        if (!e.is_app())
            return;
        if (e.decl().name().str() != "and")
            return;
        for (unsigned i = 0; i < e.num_args(); ++i)
            collect_asserted_eqP_rec(e.arg(i), atoms);
    }

    void collect_asserted_eqP(const std::vector<expr> &asserts, std::vector<expr> &atoms)
    {
        for (const expr &a : asserts)
            collect_asserted_eqP_rec(a, atoms);
    }

    void collect_eqmodP1_rec(const expr &e, std::vector<expr> &atoms)
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

    int count_rewrite_vars(const std::vector<expr> &roots)
    {
        std::unordered_set<std::string> vars;
        for (const expr &r : roots)
            collect_vars_rec(r, vars);
        return (int)vars.size();
    }

    expr simplify_assertion_rec(const expr &e,
                                const PolyDecls &d,
                                const RewriteOptions &options,
                                RewriteStats &stats)
    {
        if (!e.is_app())
            return e;
        if (e.decl().name().str() == "eqP" && e.num_args() == 2)
        {
            expr a = simplify_poly(e.arg(0), d);
            expr b = simplify_poly(e.arg(1), d);
            if (equivalent_poly(a, b, {}, d, options, stats))
                return e.ctx().bool_val(true);
            return mk_eqp(d, a, b);
        }
        if (e.decl().name().str() == "eqmodP1" && e.num_args() == 3)
        {
            expr m = simplify_poly(e.arg(2), d);
            std::vector<expr> active_moduli{m};
            expr a = normalize_poly_under_moduli(e.arg(0), active_moduli, d, options, stats);
            expr b = normalize_poly_under_moduli(e.arg(1), active_moduli, d, options, stats);
            if (equivalent_poly(a, b, active_moduli, d, options, stats))
                return e.ctx().bool_val(true);
            return mk_eqmodp1(d, a, b, m);
        }

        std::vector<expr> args;
        args.reserve(e.num_args());
        bool any = false;
        for (unsigned i = 0; i < e.num_args(); ++i)
        {
            expr a = simplify_assertion_rec(e.arg(i), d, options, stats);
            any = any || !same_ast(a, e.arg(i));
            args.push_back(a);
        }
        if (!any)
            return e.simplify();
        return rebuild_app(e, args).simplify();
    }

    expr rewrite_assertion(const expr &assertion,
                           RewriteEnv &env,
                           const RewriteOptions &options,
                           RewriteStats &stats)
    {
        expr r = apply_rules_with_env(assertion, env);
        return simplify_assertion_rec(r, env.d, options, stats).simplify();
    }

    void collect_rule_atoms_rec(const expr &e, std::unordered_set<std::string> &out)
    {
        if (is_poly_variable(e))
        {
            out.insert(variable_key(e));
            return;
        }
        if (!e.is_app())
            return;
        for (unsigned i = 0; i < e.num_args(); ++i)
            collect_rule_atoms_rec(e.arg(i), out);
    }

    PolyRewriteRule to_legacy_rule(const RewriteRule &r, const PolyDecls &d)
    {
        PolyRewriteRule rr;
        rr.kind = PolyRewriteRule::Kind::ExprRhs;
        rr.source_label = r.source_label;
        rr.is_modular = r.is_modular;
        collect_rule_atoms_rec(r.rhs, rr.rhs_atoms);

        expr rhs_int(r.rhs.ctx());
        if (poly_to_int_expr(r.rhs, d, rhs_int))
        {
            rr.rhs_int = rhs_int;
            mpz_class k;
            if (parse_mpz_numeral(rhs_int, k))
            {
                if (k == 0)
                {
                    rr.kind = PolyRewriteRule::Kind::ToZero;
                    rr.to_zero = true;
                }
                else
                {
                    rr.kind = PolyRewriteRule::Kind::ToConst;
                    rr.to_const = true;
                    rr.const_value = k;
                }
            }
        }
        return rr;
    }

    bool is_true_expr(const expr &e)
    {
        return e.is_bool() && e.is_true();
    }

} // namespace

RewriteResult rewrite_assignments(const std::vector<z3::expr> &ideal_generators,
                                  const z3::expr &target,
                                  const std::vector<z3::expr> &moduli,
                                  RewriteOptions options)
{
    RewriteResult disabled(target);
    if (!options.enable_rewriting)
    {
        disabled.residual_generators = ideal_generators;
        return disabled;
    }

    std::vector<expr> roots = ideal_generators;
    roots.push_back(target);
    roots.insert(roots.end(), moduli.begin(), moduli.end());
    PolyDecls d = collect_decls(roots);
    if (!d.pconst)
        throw std::runtime_error("rewrite_assignments: PConst constructor not found");
    ScopedSimplifyMemo simplify_scope;

    try
    {
        return try_dag_rewrite(ideal_generators, target, moduli, d, options);
    }
    catch (const CircularDependency &)
    {
        return functional_worklist_rewrite(ideal_generators, target, moduli, d, options);
    }
}

RewriteTwoPhaseResult rewrite_assignments_two_phase(
    const std::vector<AnnotatedPolynomial> &ideal_polynomials,
    const std::vector<AnnotatedPostcondition> &postconditions,
    const std::vector<z3::expr> &moduli,
    RewriteOptions options)
{
    RewriteTwoPhaseResult out{ideal_polynomials, postconditions, {}, {}, {}};
    if (!options.enable_rewriting)
        return out;

    std::vector<expr> roots;
    for (const auto &p : ideal_polynomials)
        roots.push_back(p.polynomial);
    for (const auto &p : postconditions)
    {
        roots.push_back(p.postcondition);
        roots.push_back(p.polynomial);
        roots.insert(roots.end(), p.moduli.begin(), p.moduli.end());
    }
    roots.insert(roots.end(), moduli.begin(), moduli.end());
    if (roots.empty())
        return out;
    PolyDecls d = collect_decls(roots);
    if (!d.pconst)
        return out;
    ScopedSimplifyMemo simplify_scope;

    auto post_moduli = [&](const AnnotatedPostcondition &p)
    {
        std::vector<expr> active = moduli;
        active.insert(active.end(), p.moduli.begin(), p.moduli.end());
        return active;
    };

    for (auto &p : out.postconditions)
        p.polynomial = normalize_poly_under_moduli(p.polynomial, post_moduli(p), d, options, out.stats);
    if (ideal_polynomials.empty())
        return out;

    std::vector<AnnotatedPolynomial> finished;
    std::deque<AnnotatedPolynomial> todo(out.ideal_polynomials.begin(), out.ideal_polynomials.end());
    for (std::size_t tp_iter = 0; !todo.empty(); ++tp_iter)
    {
        AnnotatedPolynomial cur = todo.front();
        todo.pop_front();
        std::vector<expr> others;
        for (const auto &p : finished)
            others.push_back(p.polynomial);
        for (const auto &p : todo)
            others.push_back(p.polynomial);
        for (const auto &p : out.postconditions)
        {
            others.push_back(p.polynomial);
            others.insert(others.end(), p.moduli.begin(), p.moduli.end());
        }

        GeneratorInfo info(cur.polynomial, simplify_poly(cur.polynomial, d), false, true,
                           "tp-i" + std::to_string(tp_iter));
        auto pat = extract_one_assignment(info, others, moduli, d, options, out.stats, out.diagnostics);
        if (!pat)
        {
            finished.push_back(cur);
            continue;
        }

        std::vector<RewriteRule> single{pat->rule};
        out.rules_used.push_back(pat->rule);
        for (auto &p : finished)
            p.polynomial = normalize_poly_under_moduli(apply_rules(p.polynomial, single, d),
                                                       moduli, d, options, out.stats);
        for (auto &p : todo)
            p.polynomial = normalize_poly_under_moduli(apply_rules(p.polynomial, single, d),
                                                       moduli, d, options, out.stats);
        for (auto &p : out.postconditions)
        {
            p.polynomial = simplify_poly(apply_rules(p.polynomial, single, d), d);
            for (auto &m : p.moduli)
                m = simplify_poly(apply_rules(m, single, d), d);
            p.polynomial = normalize_poly_under_moduli(p.polynomial, post_moduli(p), d, options, out.stats);
        }
    }
    out.ideal_polynomials = std::move(finished);
    return out;
}

RewriteResult run_rewriting_pipeline(z3::context &ctx,
                                     const std::vector<z3::expr> &input_asserts,
                                     const RewriteOptions &option,
                                     util::Logger &log)
{
    const auto rewrite_t0 = std::chrono::steady_clock::now();
    expr zero = ctx.int_val(0);
    RewriteResult out(zero);
    out.asserts = input_asserts;

    std::vector<expr> eqps_before;
    std::vector<expr> asserted_eqps_before;
    std::vector<expr> eqmods_before;
    for (const expr &a : input_asserts)
    {
        collect_eqP_rec(a, eqps_before);
        collect_eqmodP1_rec(a, eqmods_before);
    }
    collect_asserted_eqP(input_asserts, asserted_eqps_before);
    out.generators_before = (int)(eqps_before.size() + eqmods_before.size());
    out.unique_vars_before = count_rewrite_vars(input_asserts);

    if (!option.enable_rewriting)
    {
        out.generators_after = out.generators_before;
        out.unique_vars_after = out.unique_vars_before;
        const auto rewrite_t1 = std::chrono::steady_clock::now();
        LOG_INFO(log, "rewrite", "[rewrite] mode: disabled"
                                    " time=" +
                                      util::fmt_duration(rewrite_t1 - rewrite_t0));
        return out;
    }

    std::vector<expr> roots = input_asserts;
    PolyDecls d = collect_decls(roots);
    if (!d.pconst)
    {
        const auto rewrite_t1 = std::chrono::steady_clock::now();
        LOG_WARN(log, "rewrite", "[rewrite] no PConst constructor found; skipping rewriting"
                                  " time=" +
                                    util::fmt_duration(rewrite_t1 - rewrite_t0));
        return out;
    }
    ScopedSimplifyMemo simplify_scope;
    expr poly_zero = mk_pconst_mpz(d, ctx, 0);

    RewriteOptions options = option;
    if (option.preserve_eqmodp1_vars)
    {
        std::unordered_set<std::string> suppressed;
        for (const expr &em : eqmods_before)
        {
            collect_vars_rec(em.arg(0), suppressed);
            collect_vars_rec(em.arg(1), suppressed);
            collect_vars_rec(em.arg(2), suppressed);
        }
        options.suppressed_lhs_keys = std::move(suppressed);
    }

    // Assertion-level rewriting extracts assignments only from eqP atoms that
    // are unconditionally asserted: either the assertion itself, or below only
    // top-level conjunctions. Other nested eqP atoms are not known true until
    // the solver fixes them to true; the propagator handles those later.
    // eqmodP1 is rewritten by the resulting environment but is not used as an
    // equality assignment because that would be unsound as an SMT assertion.
    std::vector<expr> ideal;
    ideal.reserve(asserted_eqps_before.size());
    for (const expr &eqp : asserted_eqps_before)
        ideal.push_back(mk_psub(d, eqp.arg(0), eqp.arg(1)));

    RewriteResult core(poly_zero);
    try
    {
        core = try_dag_rewrite(ideal, poly_zero, {}, d, options);
    }
    catch (const CircularDependency &)
    {
        core = functional_worklist_rewrite(ideal, poly_zero, {}, d, options);
    }

    out.residual_generators = core.residual_generators;
    out.rewritten_target = core.rewritten_target;
    out.rules_used = core.rules_used;
    out.used_worklist_fallback = core.used_worklist_fallback;
    out.dag_rounds = core.dag_rounds;
    out.stats = core.stats;
    out.diagnostics = core.diagnostics;
    out.rewrite_skipped_log = core.diagnostics;
    if (core.used_worklist_fallback)
        out.rewrite_dropped_cycles.push_back("worklist fallback used");

    for (const RewriteRule &r : core.rules_used)
    {
        const std::string key = variable_key(r.lhs);
        out.rewrite_rules[key] = to_legacy_rule(r, d);
    }
    out.expr_rule_count = out.rewrite_rules.size();

    std::vector<expr> rewritten_asserts;
    rewritten_asserts.reserve(input_asserts.size());
    RewriteEnv assertion_env(core.rules_used, d);
    for (const expr &a : input_asserts)
    {
        expr rw = rewrite_assertion(a, assertion_env, options, out.stats);
        if (!is_true_expr(rw))
            rewritten_asserts.push_back(rw);
    }
    out.asserts = std::move(rewritten_asserts);

    std::vector<expr> eqps_after;
    std::vector<expr> eqmods_after;
    for (const expr &a : out.asserts)
    {
        collect_eqP_rec(a, eqps_after);
        collect_eqmodP1_rec(a, eqmods_after);
    }
    out.generators_after = (int)(eqps_after.size() + eqmods_after.size());
    out.unique_vars_after = count_rewrite_vars(out.asserts);

    const auto rewrite_t1 = std::chrono::steady_clock::now();
    std::ostringstream summary;
    summary << "[rewrite] input_generators=" << out.generators_before
            << " asserted_eqP=" << asserted_eqps_before.size()
            << " assignments=" << out.rules_used.size()
            << " residual_generators=" << out.residual_generators.size()
            << " dag_rounds=" << out.dag_rounds
            << " worklist=" << (out.used_worklist_fallback ? "yes" : "no")
            << " singular_nf=" << out.stats.singular_nf_checks
            << " singular_zero=" << out.stats.singular_zero_reductions
            << " singular_failures=" << out.stats.singular_failures
            << " time=" << util::fmt_duration(rewrite_t1 - rewrite_t0);
    LOG_INFO(log, "rewrite", summary.str());

    if (!out.rewrite_rules.empty())
    {
        std::vector<std::string> lines;
        for (const auto &kv : out.rewrite_rules)
            lines.push_back("    " + pretty_rewrite_atom_name(kv.first) + " -> " + rule_rhs_pretty(kv.second) +
                            " [" + kv.second.source_label + "]");
        std::sort(lines.begin(), lines.end());
        std::ostringstream oss;
        oss << "[rewrite] substitutions (" << lines.size() << "):\n";
        for (const auto &line : lines)
            oss << line << "\n";
        if (!out.rewrite_skipped_log.empty())
        {
            oss << "  skipped (" << out.rewrite_skipped_log.size() << "):\n";
            for (const std::string &sk : out.rewrite_skipped_log)
                oss << "    " << sk << "\n";
        }
        LOG_INFO(log, "rewrite", oss.str());
    }

    return out;
}

namespace
{

    const char *k_selftest_prelude = R"PRE(
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
)PRE";

    std::vector<expr> parse_assertions(context &ctx, const std::string &body)
    {
        std::string smt = "(set-logic ALL)\n";
        smt += k_selftest_prelude;
        smt += "\n";
        smt += body;
        smt += "\n(check-sat)\n";
        Z3_ast_vector v = Z3_parse_smtlib2_string((Z3_context)ctx, smt.c_str(), 0, nullptr, nullptr, 0, nullptr, nullptr);
        Z3_error_code ec = Z3_get_error_code((Z3_context)ctx);
        if (ec != Z3_OK)
            throw z3::exception(Z3_get_error_msg((Z3_context)ctx, ec));
        unsigned n = Z3_ast_vector_size((Z3_context)ctx, v);
        std::vector<expr> out;
        for (unsigned i = 0; i < n; ++i)
            out.emplace_back(ctx, Z3_ast_vector_get((Z3_context)ctx, v, i));
        return out;
    }

    expr first_eqp_diff(const std::vector<expr> &asserts, const PolyDecls &d)
    {
        std::vector<expr> eqps;
        for (const expr &a : asserts)
            collect_eqP_rec(a, eqps);
        if (eqps.empty())
            throw std::runtime_error("selftest expected eqP");
        return mk_psub(d, eqps[0].arg(0), eqps[0].arg(1));
    }

    expr last_eqp_diff(const std::vector<expr> &asserts, const PolyDecls &d)
    {
        std::vector<expr> eqps;
        for (const expr &a : asserts)
            collect_eqP_rec(a, eqps);
        if (eqps.empty())
            throw std::runtime_error("selftest expected eqP");
        const expr &e = eqps.back();
        return mk_psub(d, e.arg(0), e.arg(1));
    }

    bool equivalent_for_test(const expr &a, const expr &b, const PolyDecls &d)
    {
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        RewriteStats stats;
        try
        {
            return equivalent_poly(simplify_poly(a, d), simplify_poly(b, d), {}, d, opts, stats);
        }
        catch (const std::exception &ex)
        {
            std::cout << "  equivalence exception: " << ex.what()
                      << "\n    lhs=" << a.to_string()
                      << "\n    rhs=" << b.to_string() << "\n";
            return false;
        }
    }

    bool check(bool cond, const std::string &msg)
    {
        if (!cond)
            std::cout << "  FAIL: " << msg << "\n";
        return cond;
    }

    bool test_rule_target(const std::string &name,
                          const std::string &body,
                          const std::string &target_expr,
                          const std::string &expected_expr,
                          bool expect_rule,
                          bool subexpr_rules = false)
    {
        std::cout << "[selftest] " << name << "\n";
        context ctx;
        std::vector<expr> asserts = parse_assertions(ctx, body);
        std::vector<expr> roots = asserts;
        std::vector<expr> t = parse_assertions(ctx, body + "(assert (eqP " + target_expr + " " + expected_expr + "))");
        roots.insert(roots.end(), t.begin(), t.end());
        PolyDecls d = collect_decls(roots);
        expr diff = first_eqp_diff(asserts, d);
        expr target = last_eqp_diff(parse_assertions(ctx, body + "(assert (eqP " + target_expr + " (PConst 0)))"), d);
        expr expected = last_eqp_diff(parse_assertions(ctx, body + "(assert (eqP " + expected_expr + " (PConst 0)))"), d);
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        opts.use_subexpression_rules = subexpr_rules;
        RewriteResult rr = rewrite_assignments({diff}, target, {}, opts);
        bool ok = true;
        ok &= check((!rr.rules_used.empty()) == expect_rule, expect_rule ? "missing rule" : "unexpected rule");
        if (expect_rule)
            ok &= check(equivalent_for_test(rr.rewritten_target, expected, d),
                        "target mismatch: got " + rr.rewritten_target.to_string() + " expected " + expected.to_string());
        if (ok)
            std::cout << "  OK\n";
        return ok;
    }

} // namespace

int run_rewrite_selftests()
{
    int pass = 0;
    int total = 0;
    auto run = [&](bool ok)
    {
        ++total;
        if (ok)
            ++pass;
    };

    run(test_rule_target("x - y - 1 gives x := y + 1",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PSub (PSub (PConst x) (PConst y)) (PConst 1)) (PConst 0)))",
                         "(PConst x)", "(PAdd (PConst y) (PConst 1))", true));

    run(test_rule_target("x - y gives x := y",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PSub (PConst x) (PConst y)) (PConst 0)))",
                         "(PConst x)", "(PConst y)", true));

    run(test_rule_target("y - x gives y := x",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PSub (PConst y) (PConst x)) (PConst 0)))",
                         "(PConst y)", "(PConst x)", true));

    run(test_rule_target("y + 1 - x gives x := y + 1",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PSub (PAdd (PConst y) (PConst 1)) (PConst x)) (PConst 0)))",
                         "(PConst x)", "(PAdd (PConst y) (PConst 1))", true));

    run(test_rule_target("x + y - z gives z := x + y",
                         "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
                         "(assert (eqP (PSub (PAdd (PConst x) (PConst y)) (PConst z)) (PConst 0)))",
                         "(PConst z)", "(PAdd (PConst x) (PConst y))", true));

    run(test_rule_target("x + x - y gives y := 2*x",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PSub (PAdd (PConst x) (PConst x)) (PConst y)) (PConst 0)))",
                         "(PConst y)", "(PMul (PConst 2) (PConst x))", true, false));

    run(test_rule_target("x*y - z gives z := x*y",
                         "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
                         "(assert (eqP (PSub (PMul (PConst x) (PConst y)) (PConst z)) (PConst 0)))",
                         "(PConst z)", "(PMul (PConst x) (PConst y))", true, false));

    run(test_rule_target("x^2 - y gives y := x^2",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PSub (PPow (PConst x) 2) (PConst y)) (PConst 0)))",
                         "(PConst y)", "(PPow (PConst x) 2)", true, false));

    run(test_rule_target("x^2 + y gives y := -x^2",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PAdd (PPow (PConst x) 2) (PConst y)) (PConst 0)))",
                         "(PConst y)", "(PNeg (PPow (PConst x) 2))", true, false));

    run(test_rule_target("x^2 + x gives no assignment",
                         "(declare-const x Int)"
                         "(assert (eqP (PAdd (PPow (PConst x) 2) (PConst x)) (PConst 0)))",
                         "(PConst x)", "(PConst x)", false, false));

    run(test_rule_target("x*y + x gives no assignment",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PAdd (PMul (PConst x) (PConst y)) (PConst x)) (PConst 0)))",
                         "(PConst x)", "(PConst x)", false, false));

    run(test_rule_target("2*x - y gives y := 2*x",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PSub (PMul (PConst 2) (PConst x)) (PConst y)) (PConst 0)))",
                         "(PConst y)", "(PMul (PConst 2) (PConst x))", true, false));

    {
        std::cout << "[selftest] DAG chain rewrites x to 2\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
                                        "(assert (eqP (PConst x) (PAdd (PConst y) (PConst 1))))"
                                        "(assert (eqP (PConst y) (PAdd (PConst z) (PConst 1))))"
                                        "(assert (eqP (PConst z) (PConst 0)))");
        PolyDecls d = collect_decls(asserts);
        std::vector<expr> eqps;
        for (const expr &a : asserts)
            collect_eqP_rec(a, eqps);
        std::vector<expr> ideal;
        for (const expr &e : eqps)
            ideal.push_back(mk_psub(d, e.arg(0), e.arg(1)));
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        RewriteResult rr = rewrite_assignments(ideal, eqps[0].arg(0), {}, opts);
        bool ok = check(equivalent_for_test(rr.rewritten_target, mk_pconst_mpz(d, ctx, 2), d), "x did not rewrite to 2");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] residual and target rewriting\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
                                        "(assert (eqP (PSub (PConst x) (PAdd (PConst y) (PConst 1))) (PConst 0)))"
                                        "(assert (eqP (PAdd (PMul (PConst 2) (PConst y)) (PAdd (PConst x) (PConst z))) (PConst 0)))");
        PolyDecls d = collect_decls(asserts);
        std::vector<expr> eqps;
        for (const expr &a : asserts)
            collect_eqP_rec(a, eqps);
        std::vector<expr> ideal{mk_psub(d, eqps[0].arg(0), eqps[0].arg(1)), mk_psub(d, eqps[1].arg(0), eqps[1].arg(1))};
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        expr target_poly = mk_padd(d, mk_decl_app(ctx, d.pconst, {ctx.int_const("x")}),
                                   mk_decl_app(ctx, d.pconst, {ctx.int_const("z")}));
        RewriteResult rr = rewrite_assignments(ideal, target_poly, {}, opts);
        expr expected = mk_pmul(d, mk_pconst_mpz(d, ctx, -2), mk_decl_app(ctx, d.pconst, {ctx.int_const("y")}));
        bool ok = check(rr.residual_generators.empty(), "residual was not fully rewritten");
        ok &= check(equivalent_for_test(rr.rewritten_target, expected, d), "target not fully rewritten through affine assignments");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] cycle triggers worklist fallback and keeps residual\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const y Int)"
                                        "(assert (eqP (PConst x) (PAdd (PConst y) (PConst 1))))"
                                        "(assert (eqP (PConst y) (PAdd (PConst x) (PConst 1))))");
        PolyDecls d = collect_decls(asserts);
        std::vector<expr> eqps;
        for (const expr &a : asserts)
            collect_eqP_rec(a, eqps);
        std::vector<expr> ideal{mk_psub(d, eqps[0].arg(0), eqps[0].arg(1)), mk_psub(d, eqps[1].arg(0), eqps[1].arg(1))};
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        RewriteResult rr = rewrite_assignments(ideal, eqps[0].arg(0), {}, opts);
        bool ok = check(rr.used_worklist_fallback, "worklist fallback not used");
        ok &= check(!rr.residual_generators.empty(), "cycle residual was dropped");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] duplicate lhs handling\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const y Int)"
                                        "(assert (eqP (PConst x) (PAdd (PConst y) (PConst 1))))"
                                        "(assert (eqP (PConst x) (PAdd (PConst y) (PConst 1))))"
                                        "(assert (eqP (PConst x) (PAdd (PConst y) (PConst 2))))");
        PolyDecls d = collect_decls(asserts);
        std::vector<expr> eqps;
        for (const expr &a : asserts)
            collect_eqP_rec(a, eqps);
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        std::vector<expr> same_input{mk_psub(d, eqps[0].arg(0), eqps[0].arg(1)),
                                     mk_psub(d, eqps[1].arg(0), eqps[1].arg(1))};
        std::vector<expr> conflict_input{mk_psub(d, eqps[0].arg(0), eqps[0].arg(1)),
                                         mk_psub(d, eqps[2].arg(0), eqps[2].arg(1))};
        RewriteResult same = rewrite_assignments(same_input, eqps[0].arg(0), {}, opts);
        RewriteResult conflict_default = rewrite_assignments(conflict_input, eqps[0].arg(0), {}, opts);

        RewriteOptions reject_dups = opts;
        reject_dups.reject_duplicate_lhs = true;
        RewriteResult duplicate_rejected = rewrite_assignments(same_input, eqps[0].arg(0), {}, reject_dups);

        RewriteOptions reject_conflicts = opts;
        reject_conflicts.reject_conflicting_lhs = true;
        RewriteResult conflict_rejected = rewrite_assignments(conflict_input, eqps[0].arg(0), {}, reject_conflicts);

        bool ok = check(same.rules_used.size() == 1, "equivalent duplicate did not keep one rule by default");
        ok &= check(conflict_default.rules_used.size() == 1 && !conflict_default.residual_generators.empty(),
                    "conflicting duplicate was dropped by default");
        ok &= check(duplicate_rejected.rules_used.empty() && !duplicate_rejected.residual_generators.empty(),
                    "duplicate lhs option did not reject duplicates");
        ok &= check(conflict_rejected.rules_used.empty() && conflict_rejected.residual_generators.size() == 2,
                    "conflicting lhs option did not reject conflicts");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] assertion rewrite ignores nested eqP until fixed true\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const guard Bool)"
                                        "(assert (or guard (eqP (PConst x) (PConst 0))))");
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        util::Logger log;
        log.set_global(util::LogLevel::Error);
        RewriteResult rr = run_rewriting_pipeline(ctx, asserts, opts, log);
        bool ok = check(rr.rules_used.empty(), "nested eqP was used as an unconditional rewrite");
        ok &= check(rr.asserts.size() == asserts.size(), "nested eqP assertion was rewritten away");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] assertion rewrite uses top-level conjunct eqP\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const y Int)"
                                        "(assert (and (eqP (PConst x) (PConst 1))"
                                        "             (eqP (PConst y) (PConst x))))");
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        util::Logger log;
        log.set_global(util::LogLevel::Error);
        RewriteResult rr = run_rewriting_pipeline(ctx, asserts, opts, log);
        bool ok = check(rr.rules_used.size() == 2, "top-level conjunct eqP was not used for rewriting");
        ok &= check(rr.asserts.empty(), "top-level conjunct eqP assertion was not rewritten away");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] eqmodP1 variables rewrite by default\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const y Int)"
                                        "(assert (eqP (PConst x) (PConst 1)))"
                                        "(assert (not (eqmodP1 (PConst x) (PConst y) (PConst 7))))");
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        util::Logger log;
        log.set_global(util::LogLevel::Error);
        RewriteResult rr = run_rewriting_pipeline(ctx, asserts, opts, log);
        std::vector<expr> ems;
        for (const expr &a : rr.asserts)
            collect_eqmodP1_rec(a, ems);
        PolyDecls d = collect_decls(rr.asserts);
        bool ok = check(ems.size() == 1, "rewritten eqmodP1 atom missing");
        if (ok)
            ok &= check(equivalent_for_test(ems[0].arg(0), mk_pconst_mpz(d, ctx, 1), d),
                        "eqmodP1 lhs was not rewritten from asserted eqP");

        RewriteOptions preserve = opts;
        preserve.preserve_eqmodp1_vars = true;
        RewriteResult kept = run_rewriting_pipeline(ctx, asserts, preserve, log);
        bool kept_rule = false;
        for (const RewriteRule &r : kept.rules_used)
            kept_rule = kept_rule || variable_key(r.lhs) == "x";
        ok &= check(!kept_rule, "preserve mode still extracted eqmodP1 lhs rule");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] modular assignment requires active modulus\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const y Int)"
                                        "(assert (eqmodP1 (PConst x) (PConst y) (PConst 7)))");
        std::vector<expr> ems;
        for (const expr &a : asserts)
            collect_eqmodP1_rec(a, ems);
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        RewriteResult no = rewrite_assignments({ems[0]}, ems[0].arg(0), {}, opts);
        RewriteResult yes = rewrite_assignments({ems[0]}, ems[0].arg(0), {ems[0].arg(2)}, opts);
        bool ok = check(no.rules_used.empty(), "modular assignment accepted without modulus");
        ok &= check(!yes.rules_used.empty(), "modular assignment rejected with active modulus");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] modular common pattern requires active modulus\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const y Int)(declare-const m Int)"
                                        "(assert (eqP (PSub (PSub (PConst x) (PConst y)) (PConst m)) (PConst 0)))");
        PolyDecls d = collect_decls(asserts);
        std::vector<expr> eqps;
        for (const expr &a : asserts)
            collect_eqP_rec(a, eqps);
        expr residual = first_eqp_diff(asserts, d);
        expr modulus = eqps[0].arg(0).arg(1);
        expr target = eqps[0].arg(0).arg(0).arg(0);
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        RewriteResult inactive = rewrite_assignments({residual}, target, {}, opts);
        RewriteResult active = rewrite_assignments({residual}, target, {modulus}, opts);
        bool ok = check(equivalent_for_test(inactive.rewritten_target, target, d),
                        "inactive modular common pattern rewrote x without active modulus");
        ok &= check(equivalent_for_test(active.rewritten_target,
                                        eqps[0].arg(0).arg(0).arg(1), d),
                    "active modular common pattern did not rewrite x to y");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] active modulus rewrites target multiples to zero\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const m Int)"
                                        "(assert (eqP (PConst x) (PConst 0)))");
        PolyDecls d = collect_decls(asserts);
        expr x = mk_decl_app(ctx, d.pconst, {ctx.int_const("x")});
        expr m = mk_decl_app(ctx, d.pconst, {ctx.int_const("m")});
        expr target = mk_padd(d, x, mk_pmul(d, mk_pconst_mpz(d, ctx, 3), m));
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        RewriteResult rr = rewrite_assignments({}, target, {m}, opts);
        bool ok = check(equivalent_for_test(rr.rewritten_target, x, d),
                        "target multiple of active modulus was not rewritten to zero");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] active modulus rewrites affine scalar multiples to zero\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const y Int)"
                                        "(assert (eqP (PConst x) (PConst 0)))");
        PolyDecls d = collect_decls(asserts);
        expr x = mk_decl_app(ctx, d.pconst, {ctx.int_const("x")});
        expr y = mk_decl_app(ctx, d.pconst, {ctx.int_const("y")});
        expr two = mk_pconst_mpz(d, ctx, 2);
        expr target = mk_psub(d, mk_pmul(d, two, x), mk_pmul(d, two, y));
        expr modulus = mk_psub(d, x, y);
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        RewriteResult rr = rewrite_assignments({}, target, {modulus}, opts);
        bool ok = check(equivalent_for_test(rr.rewritten_target, mk_pconst_mpz(d, ctx, 0), d),
                        "affine multiple 2*x - 2*y was not rewritten to zero under modulus x-y");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] active modulus simplifies generators before extracting rules\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const m Int)(declare-const z Int)"
                                        "(assert (eqP (PSub (PAdd (PConst x) (PMul (PConst 3) (PConst m))) (PConst z)) (PConst 0)))");
        PolyDecls d = collect_decls(asserts);
        std::vector<expr> eqps;
        for (const expr &a : asserts)
            collect_eqP_rec(a, eqps);
        expr residual = mk_psub(d, eqps[0].arg(0), eqps[0].arg(1));
        expr x = mk_decl_app(ctx, d.pconst, {ctx.int_const("x")});
        expr m = mk_decl_app(ctx, d.pconst, {ctx.int_const("m")});
        expr z = mk_decl_app(ctx, d.pconst, {ctx.int_const("z")});
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        RewriteResult rr = rewrite_assignments({residual}, x, {m}, opts);
        bool ok = check(equivalent_for_test(rr.rewritten_target, z, d),
                        "active modulus simplification did not expose the source assignment direction");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] eqmodP1 arguments rewrite by their own modulus\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const m Int)"
                                        "(assert (eqmodP1 (PAdd (PConst x) (PMul (PConst 3) (PConst m))) (PConst x) (PConst m)))");
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        util::Logger log;
        log.set_global(util::LogLevel::Error);
        RewriteResult rr = run_rewriting_pipeline(ctx, asserts, opts, log);
        bool ok = check(rr.asserts.empty(), "eqmodP1 did not reduce to true after dropping modulus multiple");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    {
        std::cout << "[selftest] two-phase postcondition rewrites by its modulus\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const m Int)"
                                        "(assert (eqP (PConst x) (PConst 0)))");
        PolyDecls d = collect_decls(asserts);
        expr x = mk_decl_app(ctx, d.pconst, {ctx.int_const("x")});
        expr m = mk_decl_app(ctx, d.pconst, {ctx.int_const("m")});
        expr post_poly = mk_padd(d, x, mk_pmul(d, mk_pconst_mpz(d, ctx, 3), m));
        RewriteOptions opts;
        opts.use_singular_normalization = false;
        RewriteTwoPhaseResult rr = rewrite_assignments_two_phase({}, {AnnotatedPostcondition(asserts[0], post_poly, {m})}, {}, opts);
        bool ok = check(rr.postconditions.size() == 1 &&
                            equivalent_for_test(rr.postconditions[0].polynomial, x, d),
                        "two-phase postcondition kept multiple of its modulus");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    run(test_rule_target("subexpression rule extracts separable x+x when enabled",
                         "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
                         "(assert (eqP (PSub (PAdd (PAdd (PConst x) (PConst x)) (PAdd (PConst y) (PConst y))) (PAdd (PConst z) (PConst z))) (PConst 0)))",
                         "(PAdd (PConst x) (PConst x))",
                         "(PSub (PAdd (PConst z) (PConst z)) (PAdd (PConst y) (PConst y)))",
                         true, true));

    {
        std::cout << "[selftest] Singular drops residual reducible by modulus\n";
        context ctx;
        auto asserts = parse_assertions(ctx,
                                        "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
                                        "(assert (eqP (PMul (PSub (PConst x) (PConst y)) (PConst z)) (PConst 0)))");
        PolyDecls d = collect_decls(asserts);
        expr residual = first_eqp_diff(asserts, d);
        expr modulus = mk_psub(d, mk_decl_app(ctx, d.pconst, {ctx.int_const("x")}), mk_decl_app(ctx, d.pconst, {ctx.int_const("y")}));
        RewriteOptions opts;
        opts.use_singular_normalization = true;
        opts.use_subexpression_rules = false;
        RewriteResult rr = rewrite_assignments({residual}, mk_pconst_mpz(d, ctx, 0), {modulus}, opts);
        bool ok = check(rr.residual_generators.empty(), "residual was not reduced to zero by Singular");
        if (ok)
            std::cout << "  OK\n";
        run(ok);
    }

    std::cout << "\n[selftest] " << pass << "/" << total << " passed\n";
    return pass == total ? 0 : 2;
}
