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

    bool contains_expr(const expr &root, const expr &sub)
    {
        if (same_ast(root, sub) || expr_key(root) == expr_key(sub))
            return true;
        if (!root.is_app())
            return false;
        for (unsigned i = 0; i < root.num_args(); ++i)
            if (contains_expr(root.arg(i), sub))
                return true;
        return false;
    }

    std::size_t occurs_count(const expr &root, const expr &sub)
    {
        std::size_t n = (same_ast(root, sub) || expr_key(root) == expr_key(sub)) ? 1 : 0;
        if (root.is_app())
            for (unsigned i = 0; i < root.num_args(); ++i)
                n += occurs_count(root.arg(i), sub);
        return n;
    }

    bool is_numeric_const(const expr &e, const mpz_class &v)
    {
        mpz_class k;
        return extract_poly_int_constant(e, k) && k == v;
    }

    expr simplify_poly(const expr &e, const PolyDecls &d);

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

    expr simplify_poly(const expr &e, const PolyDecls &d)
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

    expr build_affine_poly(const Affine &a, const PolyDecls &d, const std::string &skip_key = {})
    {
        context *ctxp = nullptr;
        for (const auto &kv : a.var_exprs)
        {
            ctxp = &kv.second.ctx();
            break;
        }
        if (!ctxp)
            throw std::runtime_error("build_affine_poly requires at least one variable context");

        expr acc = mk_pconst_mpz(d, *ctxp, a.constant);
        for (const auto &kv : a.coeffs)
        {
            if (kv.first == skip_key || kv.second == 0)
                continue;
            auto it = a.var_exprs.find(kv.first);
            if (it == a.var_exprs.end())
                throw std::runtime_error("affine variable expression missing");
            expr term = it->second;
            if (kv.second == 1)
                acc = mk_padd(d, acc, term);
            else if (kv.second == -1)
                acc = mk_psub(d, acc, term);
            else
                acc = mk_padd(d, acc, mk_pmul(d, mk_pconst_mpz(d, *ctxp, kv.second), term));
            acc = simplify_poly(acc, d);
        }
        return simplify_poly(acc, d);
    }

    bool affine_has_only_unit_coefficients(const Affine &a)
    {
        for (const auto &kv : a.coeffs)
            if (kv.second != 1 && kv.second != -1)
                return false;
        return true;
    }

    bool is_unit_coefficient(const mpz_class &k)
    {
        return k == 1 || k == -1;
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

    std::optional<Pattern> make_common_assignment(const expr &lhs,
                                                  const expr &rhs0,
                                                  const expr &poly,
                                                  const expr &source,
                                                  const PolyDecls &d,
                                                  bool modular,
                                                  const RewriteOptions &options,
                                                  RewriteStats &stats,
                                                  std::vector<std::string> &diagnostics,
                                                  const std::string &label)
    {
        if (!is_poly_variable(lhs))
            return std::nullopt;
        const std::string key = variable_key(lhs);
        if (options.suppressed_lhs_keys.count(key))
            return std::nullopt;
        if (options.conservative_mode && contains_multiplicative_or_power(rhs0))
            return std::nullopt;
        expr rhs = simplify_poly(rhs0, d);
        if (options.conservative_mode)
        {
            Affine rhs_aff(rhs.ctx());
            if (affine_extract_poly(rhs, d, rhs_aff) && !affine_has_only_unit_coefficients(rhs_aff))
                return std::nullopt;
        }
        if (collect_vars(rhs).count(key) || contains_expr(rhs, lhs))
        {
            ++stats.skipped_lhs_occurs_in_rhs;
            diagnostics.push_back(label + ": skipped common lhs occurs in rhs");
            return std::nullopt;
        }
        if (options.enable_expression_growth_check &&
            expr_size(rhs) > expr_size(poly) + options.max_expression_growth)
        {
            ++stats.skipped_expression_growth;
            diagnostics.push_back(label + ": skipped common expression growth");
            return std::nullopt;
        }
        RewriteRule r(lhs, rhs, source, RewriteRule::Kind::Variable, modular, label);
        return Pattern(r, key);
    }

    // Fast path from rewrite.ml:is_assignment_under_moduli before the general
    // get_rewrite_pattern fallback. This preserves syntactic assignment direction
    // for v=e/e=v and v+e1=e2 patterns.
    std::optional<Pattern> extract_common_assignment(const expr &poly,
                                                     const expr &source,
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
        if (is_poly_variable(a))
            return make_common_assignment(a, b, poly, source, d, modular, options, stats, diagnostics, label);
        if (is_poly_variable(b))
        {
            std::vector<std::string> vars;
            collect_vars_vec_rec(a, vars);
            const std::string bkey = variable_key(b);
            bool smaller_lhs_var = false;
            for (const std::string &v : vars)
                if (v < bkey)
                    smaller_lhs_var = true;
            if (!smaller_lhs_var)
                return make_common_assignment(b, a, poly, source, d, modular, options, stats, diagnostics, label);
        }

        if (is_ctor(a, "PAdd", 2))
        {
            if (is_poly_variable(a.arg(0)))
                return make_common_assignment(a.arg(0), mk_psub(d, b, a.arg(1)), poly, source, d, modular,
                                              options, stats, diagnostics, label);
            if (is_poly_variable(a.arg(1)))
                return make_common_assignment(a.arg(1), mk_psub(d, b, a.arg(0)), poly, source, d, modular,
                                              options, stats, diagnostics, label);
        }
        if (is_ctor(b, "PAdd", 2))
        {
            if (is_poly_variable(b.arg(0)))
                return make_common_assignment(b.arg(0), mk_psub(d, a, b.arg(1)), poly, source, d, modular,
                                              options, stats, diagnostics, label);
            if (is_poly_variable(b.arg(1)))
                return make_common_assignment(b.arg(1), mk_psub(d, a, b.arg(0)), poly, source, d, modular,
                                              options, stats, diagnostics, label);
        }
        return std::nullopt;
    }

    // Corresponds to rewrite.ml:get_rewrite_pattern, with the requested C++
    // conservative restriction that every affine variable coefficient must be ±1.
    std::optional<Pattern> extract_rewrite_pattern(const expr &poly,
                                                   const expr &source,
                                                   const PolyDecls &d,
                                                   bool modular,
                                                   const RewriteOptions &options,
                                                   RewriteStats &stats,
                                                   std::vector<std::string> &diagnostics,
                                                   const std::string &label)
    {
        if (auto common = extract_common_assignment(poly, source, d, modular, options, stats, diagnostics, label))
            return common;

        Affine a(poly.ctx());
        if (!affine_extract_poly(poly, d, a))
        {
            ++stats.skipped_nonlinear;
            diagnostics.push_back(label + ": skipped nonlinear");
            return std::nullopt;
        }
        if (a.coeffs.empty())
            return std::nullopt;

        std::vector<std::string> candidates;
        for (const auto &kv : a.coeffs)
        {
            if (!is_unit_coefficient(kv.second))
                continue;
            auto it = a.var_exprs.find(kv.first);
            if (it == a.var_exprs.end())
                continue;
            if (occurs_count(poly, it->second) == 1)
                candidates.push_back(kv.first);
        }
        if (candidates.empty())
        {
            ++stats.skipped_unsafe_coefficient;
            diagnostics.push_back(label + ": skipped unsafe coefficient");
            return std::nullopt;
        }
        std::sort(candidates.begin(), candidates.end());

        for (const std::string &key : candidates)
        {
            auto vit = a.var_exprs.find(key);
            if (vit == a.var_exprs.end())
                continue;
            const expr lhs = vit->second;
            if (options.suppressed_lhs_keys.count(key))
            {
                diagnostics.push_back(label + ": skipped suppressed lhs " + pretty_rewrite_atom_name(key));
                continue;
            }

            expr rest = build_affine_poly(a, d, key);
            expr rhs = (a.coeffs.at(key) == 1) ? simplify_pneg(rest, d) : rest;
            rhs = simplify_poly(rhs, d);
            if (contains_expr(rhs, lhs))
            {
                ++stats.skipped_lhs_occurs_in_rhs;
                diagnostics.push_back(label + ": skipped lhs occurs in rhs");
                continue;
            }
            if (options.enable_expression_growth_check &&
                expr_size(rhs) > expr_size(poly) + options.max_expression_growth)
            {
                ++stats.skipped_expression_growth;
                diagnostics.push_back(label + ": skipped expression growth");
                continue;
            }
            RewriteRule r(lhs, rhs, source, RewriteRule::Kind::Variable, modular, label);
            return Pattern(r, key);
        }
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

    // Corresponds to rewrite.ml:get_rewrite_pattern'.  In conservative mode we do
    // not synthesize nonlinear PMul/PPow assignments; those remain residuals.
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
            if (options.conservative_mode && contains_multiplicative_or_power(sub))
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
            return GeneratorInfo(p, p, true, true, label);
        }
        if (is_poly_ctor(g))
            return GeneratorInfo(g, simplify_poly(g, d), false, true, label);
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
        (void)moduli;
        if (!info.usable)
            return std::nullopt;
        auto pat = extract_rewrite_pattern(info.polynomial, info.residual, d, info.modular,
                                           options, stats, diagnostics, info.label);
        if (pat)
            return pat;
        if (options.use_subexpression_rules && options.enable_expr_rewriting)
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
        for (std::size_t i = 0; i < infos.size(); ++i)
        {
            std::vector<expr> others;
            others.reserve(infos.size() > 0 ? infos.size() - 1 : 0);
            for (std::size_t j = 0; j < infos.size(); ++j)
                if (i != j)
                    others.push_back(infos[j].polynomial);

            auto pat = extract_one_assignment(infos[i], others, moduli, d, options, stats, diagnostics);
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

    expr substitute_one_rec(const expr &e, const RewriteRule &r, const PolyDecls &d, bool &changed)
    {
        if (same_ast(e, r.lhs) || expr_key(e) == expr_key(r.lhs))
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
            expr child = substitute_one_rec(e.arg(i), r, d, child_changed);
            any = any || child_changed;
            args.push_back(child);
        }
        if (!any)
            return e;
        changed = true;
        return rebuild_app(e, args).simplify();
    }

    expr apply_rules(const expr &e, const std::vector<RewriteRule> &rules, const PolyDecls &d)
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

    void fill_rule_dependencies(RewriteRule &r, const std::vector<RewriteRule> &all)
    {
        std::set<std::string> deps;
        for (const RewriteRule &other : all)
            if (!same_ast(r.lhs, other.lhs) && contains_expr(r.rhs, other.lhs))
                deps.insert(variable_key(other.lhs));
        r.rhs_dependencies.assign(deps.begin(), deps.end());
    }

    std::vector<std::size_t> topo_sort_rules(const std::vector<RewriteRule> &rules)
    {
        const std::size_t n = rules.size();
        std::unordered_map<std::string, std::size_t> index;
        for (std::size_t i = 0; i < n; ++i)
            index[variable_key(rules[i].lhs)] = i;

        std::vector<std::vector<std::size_t>> deps(n);
        for (std::size_t i = 0; i < n; ++i)
        {
            for (std::size_t j = 0; j < n; ++j)
            {
                if (i != j && contains_expr(rules[i].rhs, rules[j].lhs))
                    deps[i].push_back(j);
            }
            std::sort(deps[i].begin(), deps[i].end());
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
            env.push_back(r);
        }
        for (RewriteRule &r : env)
            fill_rule_dependencies(r, env);
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
            expr r = is_poly_ctor(r0) ? simplify_poly(r0, d) : r0.simplify();
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
            ++res.dag_rounds;
            res.rules_used.insert(res.rules_used.end(), env.begin(), env.end());

            std::vector<expr> rewritten_residuals;
            rewritten_residuals.reserve(ex.residuals.size());
            for (const expr &r : ex.residuals)
                rewritten_residuals.push_back(simplify_poly(apply_rules(r, env, d), d));
            current = normalize_residuals(rewritten_residuals, moduli, d, options, res.stats);
            current_target = simplify_poly(apply_rules(current_target, env, d), d);
        }

        res.residual_generators = std::move(current);
        res.rewritten_target = current_target;
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
            poly = simplify_poly(apply_rules(poly, env, d), d);

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

        for (RewriteRule &r : env)
            fill_rule_dependencies(r, env);
        res.rules_used = env;

        std::vector<expr> final_residuals;
        for (const expr &r : residuals)
            final_residuals.push_back(simplify_poly(apply_rules(r, env, d), d));
        while (!stack.empty())
        {
            final_residuals.push_back(simplify_poly(apply_rules(stack.front(), env, d), d));
            stack.pop_front();
        }
        res.residual_generators = normalize_residuals(final_residuals, moduli, d, options, res.stats);
        res.rewritten_target = simplify_poly(apply_rules(target, env, d), d);
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

    void collect_direct_asserted_eqP(const std::vector<expr> &asserts, std::vector<expr> &atoms)
    {
        for (const expr &a : asserts)
        {
            if (is_eqP_atom(a))
                atoms.push_back(a);
        }
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
            expr a = simplify_poly(e.arg(0), d);
            expr b = simplify_poly(e.arg(1), d);
            expr m = simplify_poly(e.arg(2), d);
            if (same_ast(a, b) || expr_key(a) == expr_key(b))
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
                           const std::vector<RewriteRule> &rules,
                           const PolyDecls &d,
                           const RewriteOptions &options,
                           RewriteStats &stats)
    {
        expr r = apply_rules(assertion, rules, d);
        return simplify_assertion_rec(r, d, options, stats).simplify();
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
    if (!options.enable_rewriting || ideal_polynomials.empty())
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
    PolyDecls d = collect_decls(roots);

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
            p.polynomial = simplify_poly(apply_rules(p.polynomial, single, d), d);
        for (auto &p : todo)
            p.polynomial = simplify_poly(apply_rules(p.polynomial, single, d), d);
        for (auto &p : out.postconditions)
        {
            p.polynomial = simplify_poly(apply_rules(p.polynomial, single, d), d);
            for (auto &m : p.moduli)
                m = simplify_poly(apply_rules(m, single, d), d);
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
    expr zero = ctx.int_val(0);
    RewriteResult out(zero);
    out.asserts = input_asserts;

    std::vector<expr> eqps_before;
    std::vector<expr> direct_eqps_before;
    std::vector<expr> eqmods_before;
    for (const expr &a : input_asserts)
    {
        collect_eqP_rec(a, eqps_before);
        collect_eqmodP1_rec(a, eqmods_before);
    }
    collect_direct_asserted_eqP(input_asserts, direct_eqps_before);
    out.generators_before = (int)(eqps_before.size() + eqmods_before.size());
    out.unique_vars_before = count_rewrite_vars(input_asserts);

    if (!option.enable_rewriting)
    {
        out.generators_after = out.generators_before;
        out.unique_vars_after = out.unique_vars_before;
        LOG_INFO(log, "rewrite", "[rewrite] mode: disabled");
        return out;
    }

    std::vector<expr> roots = input_asserts;
    PolyDecls d = collect_decls(roots);
    if (!d.pconst)
    {
        LOG_WARN(log, "rewrite", "[rewrite] no PConst constructor found; skipping rewriting");
        return out;
    }
    expr poly_zero = mk_pconst_mpz(d, ctx, 0);

    RewriteOptions options = option;
    options.use_subexpression_rules = option.use_subexpression_rules && option.enable_expr_rewriting;
    if (option.suppress_expr_rhs_for_eqmodp1_atoms)
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

    // Assertion-level rewriting extracts assignments only from directly asserted
    // eqP atoms.  Nested eqP atoms inside Boolean structure are not known true
    // until the solver fixes them to true; the propagator handles those later.
    // eqmodP1 is rewritten by the resulting environment but is not used as an
    // equality assignment because that would be unsound as an SMT assertion.
    std::vector<expr> ideal;
    ideal.reserve(direct_eqps_before.size());
    for (const expr &eqp : direct_eqps_before)
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
    for (const expr &a : input_asserts)
    {
        expr rw = rewrite_assertion(a, core.rules_used, d, options, out.stats);
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

    std::ostringstream summary;
    summary << "[rewrite] input_generators=" << out.generators_before
            << " direct_eqP=" << direct_eqps_before.size()
            << " assignments=" << out.rules_used.size()
            << " residual_generators=" << out.residual_generators.size()
            << " dag_rounds=" << out.dag_rounds
            << " worklist=" << (out.used_worklist_fallback ? "yes" : "no")
            << " singular_nf=" << out.stats.singular_nf_checks
            << " singular_zero=" << out.stats.singular_zero_reductions
            << " singular_failures=" << out.stats.singular_failures;
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

    run(test_rule_target("y + 1 - x gives x := y + 1",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PSub (PAdd (PConst y) (PConst 1)) (PConst x)) (PConst 0)))",
                         "(PConst x)", "(PAdd (PConst y) (PConst 1))", true));

    run(test_rule_target("x + y - z deterministic assignment rewrites x",
                         "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
                         "(assert (eqP (PSub (PAdd (PConst x) (PConst y)) (PConst z)) (PConst 0)))",
                         "(PConst x)", "(PSub (PConst z) (PConst y))", true));

    run(test_rule_target("x + x - y gives y := 2*x",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PSub (PAdd (PConst x) (PConst x)) (PConst y)) (PConst 0)))",
                         "(PConst y)", "(PMul (PConst 2) (PConst x))", true, false));

    run(test_rule_target("x*y - z gives no assignment",
                         "(declare-const x Int)(declare-const y Int)(declare-const z Int)"
                         "(assert (eqP (PSub (PMul (PConst x) (PConst y)) (PConst z)) (PConst 0)))",
                         "(PConst z)", "(PConst z)", false, false));

    run(test_rule_target("x^2 - y gives no assignment",
                         "(declare-const x Int)(declare-const y Int)"
                         "(assert (eqP (PSub (PPow (PConst x) 2) (PConst y)) (PConst 0)))",
                         "(PConst y)", "(PConst y)", false, false));

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
