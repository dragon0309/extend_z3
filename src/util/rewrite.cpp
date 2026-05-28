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

std::string rule_rhs_pretty(const PolyRewriteRule &rr)
{
    switch (rr.kind)
    {
    case PolyRewriteRule::Kind::ToZero:
        return "0";
    case PolyRewriteRule::Kind::ToConst:
        return rr.const_value.get_str();
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
        return pretty_rewrite_atom_name(s.substr(std::strlen("PConst:")));
    if (s.rfind("PVar:", 0) == 0)
        return pretty_rewrite_atom_name(s.substr(std::strlen("PVar:")));
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

    std::string format_raw_set(std::vector<std::string> items)
    {
        std::sort(items.begin(), items.end());
        items.erase(std::unique(items.begin(), items.end()), items.end());
        std::ostringstream oss;
        oss << "{";
        for (std::size_t i = 0; i < items.size(); ++i)
        {
            if (i)
                oss << ", ";
            oss << items[i];
        }
        oss << "}";
        return oss.str();
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

    bool occurs_once_keyed(const expr &root,
                           const expr &sub,
                           const std::string &sub_key,
                           bool sub_is_var,
                           std::size_t &count)
    {
        if (expr_matches_key(root, sub, sub_key, sub_is_var) && ++count > 1)
            return false;
        if (root.is_app())
            for (unsigned i = 0; i < root.num_args(); ++i)
                if (!occurs_once_keyed(root.arg(i), sub, sub_key, sub_is_var, count))
                    return false;
        return true;
    }

    bool occurs_once(const expr &root, const expr &sub)
    {
        const bool sub_is_var = is_poly_variable(sub);
        const std::string sub_key = sub_is_var ? variable_key(sub) : expr_key(sub);
        std::size_t count = 0;
        return occurs_once_keyed(root, sub, sub_key, sub_is_var, count) && count == 1;
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
        bool changed = false;

        PolySimplifyMemoEntry(const expr &o, const expr &s, bool c) : original(o), simplified(s), changed(c) {}
    };

    using SimplifyMemo = std::unordered_map<AstCacheKey, std::vector<PolySimplifyMemoEntry>, AstCacheKeyHash>;
    thread_local SimplifyMemo *active_simplify_memo = nullptr;
    thread_local bool active_disable_rewrite_cache = false;
    thread_local bool active_verify_rewrite_lookups = false;
    thread_local std::ostream *active_rewrite_lookup_log = nullptr;

    struct RewriteLookupStats
    {
        std::size_t simplify_hits_verified = 0;
        std::size_t expanded_hits_verified = 0;
        std::size_t rewrite_memo_hits_verified = 0;
        std::size_t failures = 0;
    };

    thread_local RewriteLookupStats *active_rewrite_lookup_stats = nullptr;

    bool cache_expr_matches(const expr &cached, const expr &recomputed)
    {
        if (same_ast(cached, recomputed))
            return true;
        try
        {
            return (cached == recomputed).simplify().is_true();
        }
        catch (...)
        {
            return false;
        }
    }

    void record_lookup_verification(const char *what,
                                    const expr &original,
                                    const expr &cached,
                                    const expr &recomputed,
                                    bool *changed = nullptr,
                                    bool *recomputed_changed = nullptr)
    {
        const bool ok = cache_expr_matches(cached, recomputed) &&
                        (!changed || !recomputed_changed || *changed == *recomputed_changed);

        if (active_rewrite_lookup_stats)
        {
            if (std::strcmp(what, "simplify_poly memo") == 0)
                ++active_rewrite_lookup_stats->simplify_hits_verified;
            else if (std::strcmp(what, "expanded rewrite rule") == 0)
                ++active_rewrite_lookup_stats->expanded_hits_verified;
            else if (std::strcmp(what, "rewrite memo") == 0)
                ++active_rewrite_lookup_stats->rewrite_memo_hits_verified;
            if (!ok)
                ++active_rewrite_lookup_stats->failures;
        }

        if (active_rewrite_lookup_log)
        {
            *active_rewrite_lookup_log << "[lookup] " << what << " "
                                       << (ok ? "OK" : "FAIL") << "\n";
            if (changed && recomputed_changed)
                *active_rewrite_lookup_log << "  changed=" << (*changed ? "true" : "false")
                                           << " recomputed_changed=" << (*recomputed_changed ? "true" : "false")
                                           << "\n";
            *active_rewrite_lookup_log << "  original=" << original << "\n"
                                       << "  cached=" << cached << "\n"
                                       << "  recomputed=" << recomputed << "\n\n";
        }

        if (ok)
            return;

        std::ostringstream oss;
        oss << "rewrite lookup verification failed for " << what
            << "\n  original=" << original
            << "\n  cached=" << cached
            << "\n  recomputed=" << recomputed;
        if (changed && recomputed_changed)
            oss << "\n  cached_changed=" << (*changed ? "true" : "false")
                << "\n  recomputed_changed=" << (*recomputed_changed ? "true" : "false");
        throw std::runtime_error(oss.str());
    }

    struct ScopedLookupOverride
    {
        SimplifyMemo *previous_memo = nullptr;
        bool previous_disable = false;
        bool previous_verify = false;

        ScopedLookupOverride(SimplifyMemo *memo, bool disable_cache, bool verify_lookups)
            : previous_memo(active_simplify_memo),
              previous_disable(active_disable_rewrite_cache),
              previous_verify(active_verify_rewrite_lookups)
        {
            active_simplify_memo = memo;
            active_disable_rewrite_cache = disable_cache;
            active_verify_rewrite_lookups = verify_lookups;
        }

        ~ScopedLookupOverride()
        {
            active_simplify_memo = previous_memo;
            active_disable_rewrite_cache = previous_disable;
            active_verify_rewrite_lookups = previous_verify;
        }

        ScopedLookupOverride(const ScopedLookupOverride &) = delete;
        ScopedLookupOverride &operator=(const ScopedLookupOverride &) = delete;
    };

    struct ScopedSimplifyMemo
    {
        SimplifyMemo memo;
        RewriteLookupStats stats;
        SimplifyMemo *previous = nullptr;
        bool previous_disable = false;
        bool previous_verify = false;
        std::ostream *previous_lookup_log = nullptr;
        RewriteLookupStats *previous_lookup_stats = nullptr;

        explicit ScopedSimplifyMemo(const RewriteOptions &options = RewriteOptions{})
            : previous(active_simplify_memo),
              previous_disable(active_disable_rewrite_cache),
              previous_verify(active_verify_rewrite_lookups),
              previous_lookup_log(active_rewrite_lookup_log),
              previous_lookup_stats(active_rewrite_lookup_stats)
        {
            active_simplify_memo = &memo;
            active_disable_rewrite_cache = options.disable_rewrite_cache;
            active_verify_rewrite_lookups = options.verify_rewrite_lookups;
            active_rewrite_lookup_log = options.rewrite_lookup_log;
            active_rewrite_lookup_stats = options.rewrite_lookup_log ? &stats : nullptr;
            if (active_rewrite_lookup_log)
            {
                *active_rewrite_lookup_log << "[rewrite lookup verification]\n"
                                           << "  disable_cache="
                                           << (options.disable_rewrite_cache ? "true" : "false") << "\n"
                                           << "  verify_lookups="
                                           << (options.verify_rewrite_lookups ? "true" : "false") << "\n\n";
            }
        }

        ~ScopedSimplifyMemo()
        {
            if (active_rewrite_lookup_log && active_rewrite_lookup_stats == &stats)
            {
                *active_rewrite_lookup_log << "[summary]\n"
                                           << "  simplify_poly memo verified hits: "
                                           << stats.simplify_hits_verified << "\n"
                                           << "  expanded rewrite rule verified hits: "
                                           << stats.expanded_hits_verified << "\n"
                                           << "  rewrite memo verified hits: "
                                           << stats.rewrite_memo_hits_verified << "\n"
                                           << "  failures: " << stats.failures << "\n";
            }
            active_simplify_memo = previous;
            active_disable_rewrite_cache = previous_disable;
            active_verify_rewrite_lookups = previous_verify;
            active_rewrite_lookup_log = previous_lookup_log;
            active_rewrite_lookup_stats = previous_lookup_stats;
        }

        ScopedSimplifyMemo(const ScopedSimplifyMemo &) = delete;
        ScopedSimplifyMemo &operator=(const ScopedSimplifyMemo &) = delete;
    };

    expr simplify_poly(const expr &e, const PolyDecls &d);
    expr simplify_poly_impl(const expr &e, const PolyDecls &d);

    expr simplify_poly_uncached_for_verification(const expr &e, const PolyDecls &d)
    {
        ScopedLookupOverride guard(nullptr, true, false);
        return simplify_poly_impl(e, d);
    }

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
        if (active_disable_rewrite_cache)
            return simplify_poly_impl(e, d);

        AstCacheKey key{(Z3_context)e.ctx(), ast_id(e)};
        auto it = memo.find(key);
        if (it != memo.end())
        {
            for (const PolySimplifyMemoEntry &entry : it->second)
                if (same_ast(entry.original, e))
                {
                    if (active_verify_rewrite_lookups)
                    {
                        expr recomputed = simplify_poly_uncached_for_verification(e, d);
                        bool cached_changed = entry.changed;
                        bool recomputed_changed = !same_ast(e, recomputed);
                        record_lookup_verification("simplify_poly memo", e, entry.simplified, recomputed,
                                                   &cached_changed, &recomputed_changed);
                    }
                    return entry.simplified;
                }
        }

        expr r = simplify_poly_impl(e, d);
        memo[key].emplace_back(e, r, !same_ast(e, r));
        return r;
    }

    expr simplify_poly(const expr &e, const PolyDecls &d)
    {
        if (active_disable_rewrite_cache)
            return simplify_poly_impl(e, d);
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
            if (!occurs_once(poly, lhs))
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
            if (!occurs_once(poly, sub))
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
        std::size_t input_index = 0;

        GeneratorInfo(const expr &r, const expr &p, bool m, bool u, std::string l, std::size_t idx = 0)
            : residual(r), polynomial(p), modular(m), usable(u), label(std::move(l)), input_index(idx)
        {
        }
    };

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

    bool is_eqP_atom(const expr &e);
    bool is_true_expr(const expr &e);

    struct Extraction
    {
        struct Residual
        {
            expr polynomial;
            std::string reason;
            std::size_t input_index = 0;

            Residual(const expr &p, std::string r, std::size_t idx)
                : polynomial(p), reason(std::move(r)), input_index(idx)
            {
            }
        };

        std::vector<RewriteRule> rules;
        std::vector<Residual> residuals;
        std::vector<std::size_t> consumed_input_indices;
        std::vector<expr> input_formulas;
        std::size_t input_count = 0;
    };

    struct RewriteItem
    {
        expr formula;
        std::optional<expr> poly_view;
        bool rule_candidate = false;
        std::size_t source_index = 0;

        RewriteItem(const expr &f, std::optional<expr> p, bool candidate, std::size_t idx)
            : formula(f), poly_view(std::move(p)), rule_candidate(candidate), source_index(idx)
        {
        }
    };

    struct AssertionRewriteResult
    {
        std::vector<expr> residual_assertions;
        std::vector<RewriteRule> rules_used;
        bool used_worklist_rewrite = false;
        std::size_t dag_rounds = 0;
        RewriteStats stats;
        std::vector<std::string> diagnostics;
    };

    struct AssertionWorkItem
    {
        expr formula;
        std::unordered_set<std::string> vars;
        std::optional<expr> poly_view;
        bool rule_candidate = false;
    };

    struct AssertionRewriteTiming
    {
        std::chrono::nanoseconds make_items{0};
        std::chrono::nanoseconds extract{0};
        std::chrono::nanoseconds topo_sort{0};
        std::chrono::nanoseconds compose{0};
        std::chrono::nanoseconds build_env{0};
        std::chrono::nanoseconds residual_rewrite{0};
        std::chrono::nanoseconds final_collect{0};
        std::size_t rounds = 0;
        std::size_t items_seen = 0;
        std::size_t residual_rewrite_calls = 0;
    };

    void append_rewrite_items_rec(const expr &assertion,
                                  std::vector<RewriteItem> &items,
                                  const PolyDecls &d,
                                  std::size_t source_index)
    {
        if (is_true_expr(assertion))
            return;
        if (assertion.is_app() && assertion.decl().name().str() == "and")
        {
            for (unsigned i = 0; i < assertion.num_args(); ++i)
                append_rewrite_items_rec(assertion.arg(i), items, d, source_index);
            return;
        }

        if (is_eqP_atom(assertion))
        {
            expr poly = simplify_poly(mk_psub(d, assertion.arg(0), assertion.arg(1)), d);
            items.emplace_back(assertion, poly, true, source_index);
            return;
        }

        items.emplace_back(assertion, std::nullopt, false, source_index);
    }

    std::vector<RewriteItem> make_rewrite_items(const std::vector<expr> &assertions,
                                                const PolyDecls &d)
    {
        std::vector<RewriteItem> items;
        for (std::size_t i = 0; i < assertions.size(); ++i)
            append_rewrite_items_rec(assertions[i], items, d, i);
        return items;
    }

    std::vector<expr> formulas_from_items(const std::vector<RewriteItem> &items)
    {
        std::vector<expr> out;
        out.reserve(items.size());
        std::unordered_set<std::string> seen;
        seen.reserve(items.size());
        for (const RewriteItem &item : items)
        {
            if (is_true_expr(item.formula))
                continue;
            if (seen.insert(item.formula.to_string()).second)
                out.push_back(item.formula);
        }
        return out;
    }

    Extraction extract_assertion_item_assignments(const std::vector<RewriteItem> &items,
                                                  const std::vector<expr> &moduli,
                                                  const PolyDecls &d,
                                                  const RewriteOptions &options,
                                                  RewriteStats &stats,
                                                  std::vector<std::string> &diagnostics,
                                                  const std::string &trace_scope)
    {
        const std::string scope_prefix = trace_scope.empty() ? "" : trace_scope + "/";
        Extraction out;
        out.input_count = items.size();
        if (options.rewrite_log)
            out.input_formulas.reserve(items.size());

        std::vector<GeneratorInfo> infos;
        infos.reserve(items.size());
        for (std::size_t i = 0; i < items.size(); ++i)
        {
            if (options.rewrite_log)
                out.input_formulas.push_back(items[i].formula);
            if (!items[i].rule_candidate || !items[i].poly_view)
                continue;

            const std::string glabel = scope_prefix + "item#" + std::to_string(i);
            expr p = moduli.empty() ? *items[i].poly_view
                                    : normalize_poly_under_moduli(*items[i].poly_view, moduli, d, options, stats);
            GeneratorInfo info(items[i].formula, p, false, true, glabel, i);
            infos.push_back(info);
        }

        struct Candidate
        {
            Pattern pattern;
            std::size_t index;
            Candidate(const Pattern &p, std::size_t i) : pattern(p), index(i) {}
        };

        std::unordered_map<std::string, std::vector<Candidate>> grouped;
        grouped.reserve(infos.size());
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

        std::vector<bool> consumed(infos.size(), false);
        std::vector<std::string> residual_reasons(infos.size());
        out.rules.reserve(grouped.size());
        out.consumed_input_indices.reserve(grouped.size());
        for (auto &kv : grouped)
        {
            auto &cands = kv.second;
            const std::string lhs_name = cands.empty() ? kv.first : cands[0].pattern.rule.lhs.to_string();

            out.rules.push_back(cands[0].pattern.rule);
            out.consumed_input_indices.push_back(infos[cands[0].index].input_index);
            ++stats.rules_extracted;
            consumed[cands[0].index] = true;
            for (std::size_t i = 1; i < cands.size(); ++i)
                residual_reasons[cands[i].index] = "duplicate LHS " + lhs_name + " already assigned in this round";
        }

        std::sort(out.rules.begin(), out.rules.end(),
                  [](const RewriteRule &a, const RewriteRule &b)
                  {
                      return variable_key(a.lhs) < variable_key(b.lhs);
                  });

        for (std::size_t i = 0; i < infos.size(); ++i)
        {
            if (!has_candidate[i] || !consumed[i])
                out.residuals.emplace_back(infos[i].polynomial, residual_reasons[i], infos[i].input_index);
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
        bool disable_cache = false;
        bool verify_lookups = false;
        std::unordered_map<std::string, const RewriteRule *> by_lhs;
        std::unordered_map<std::string, expr> expanded;
        std::unordered_map<unsigned, std::vector<RewriteMemoEntry>> memo;
        std::unordered_set<std::string> active;

        RewriteEnv(const std::vector<RewriteRule> &rules_, const PolyDecls &d_,
                   const RewriteOptions &options_ = RewriteOptions{})
            : rules(rules_), d(d_), disable_cache(options_.disable_rewrite_cache),
              verify_lookups(options_.verify_rewrite_lookups)
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
        if (!env.disable_cache)
        {
            auto cached = env.expanded.find(key);
            if (cached != env.expanded.end())
            {
                if (env.verify_lookups)
                {
                    RewriteOptions verify_options;
                    verify_options.disable_rewrite_cache = true;
                    RewriteEnv check_env(env.rules, env.d, verify_options);
                    ScopedLookupOverride guard(nullptr, true, false);
                    expr recomputed = expand_variable_rule_env(key, check_env);
                    record_lookup_verification("expanded rewrite rule", cached->second, cached->second, recomputed);
                }
                return cached->second;
            }
        }

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

        if (env.disable_cache)
            return rhs;
        auto [pos, _] = env.expanded.emplace(key, rhs);
        return pos->second;
    }

    expr apply_variable_env_rec(const expr &e, RewriteEnv &env, bool &changed)
    {
        const unsigned id = ast_id(e);
        if (!env.disable_cache)
        {
            auto cached = env.memo.find(id);
            if (cached != env.memo.end())
            {
                for (const RewriteMemoEntry &entry : cached->second)
                {
                    if (same_ast(entry.original, e))
                    {
                        if (env.verify_lookups)
                        {
                            RewriteOptions verify_options;
                            verify_options.disable_rewrite_cache = true;
                            RewriteEnv check_env(env.rules, env.d, verify_options);
                            bool recomputed_changed = false;
                            ScopedLookupOverride guard(nullptr, true, false);
                            expr recomputed = apply_variable_env_rec(e, check_env, recomputed_changed);
                            bool cached_changed = entry.changed;
                            record_lookup_verification("rewrite memo", e, entry.rewritten, recomputed,
                                                       &cached_changed, &recomputed_changed);
                        }
                        changed = entry.changed;
                        return entry.rewritten;
                    }
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
                if (!env.disable_cache && env.active.find(key) == env.active.end())
                    env.memo[id].emplace_back(e, r, true);
                return r;
            }
        }
        if (!e.is_app())
        {
            changed = false;
            if (!env.disable_cache)
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
            if (!env.disable_cache)
                env.memo[id].emplace_back(e, e, false);
            return e;
        }

        changed = true;
        expr r = rebuild_app(e, args).simplify();
        if (!env.disable_cache)
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

    std::vector<std::size_t> topo_sort_rules(const std::vector<RewriteRule> &rules)
    {
        const std::size_t n = rules.size();
        std::unordered_map<std::string, std::size_t> index;
        index.reserve(n);
        std::vector<std::string> lhs_keys;
        lhs_keys.reserve(n);
        bool use_dependency_keys = true;
        for (std::size_t i = 0; i < n; ++i)
        {
            if (rules[i].kind != RewriteRule::Kind::Variable || !is_poly_variable(rules[i].lhs))
                use_dependency_keys = false;
            lhs_keys.push_back(variable_key(rules[i].lhs));
            index[lhs_keys.back()] = i;
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
        sorted.reserve(n);
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
                  { return lhs_keys[a] < lhs_keys[b]; });
        for (std::size_t i : order)
            dfs(i);
        return sorted;
    }

    std::vector<RewriteRule> compose_rules(const std::vector<RewriteRule> &rules,
                                           const std::vector<std::size_t> &sorted,
                                           const PolyDecls &d,
                                           const RewriteOptions &options)
    {
        std::vector<RewriteRule> env;
        env.reserve(rules.size());
        RewriteEnv rewrite_env(env, d, options);
        for (std::size_t idx : sorted)
        {
            const RewriteRule &src = rules[idx];
            expr rhs = simplify_poly(apply_rules_with_env(src.rhs, rewrite_env), d);
            if (contains_expr(rhs, src.lhs))
                throw CircularDependency();
            RewriteRule r(src.lhs, rhs, src.source_generator, src.kind, src.is_modular, src.source_label);
            r.rhs_dependencies = collect_sorted_vars(rhs);
            env.push_back(r);
            rewrite_env.memo.clear();
            if (rewrite_env.all_variable_rules && r.kind == RewriteRule::Kind::Variable && is_poly_variable(r.lhs))
            {
                std::string key = variable_key(env.back().lhs);
                rewrite_env.by_lhs.emplace(key, &env.back());
                rewrite_env.expanded.erase(key);
            }
            else
            {
                rewrite_env.all_variable_rules = false;
                rewrite_env.by_lhs.clear();
                rewrite_env.expanded.clear();
            }
        }
        return env;
    }

    void write_rule_list(std::ostream &os, const std::vector<RewriteRule> &rules, const PolyDecls &d)
    {
        (void)d;
        if (rules.empty())
        {
            os << "(none)\n";
            return;
        }
        for (const RewriteRule &r : rules)
            os << r.lhs.to_string() << " := " << r.rhs.to_string() << "\n";
    }

    std::vector<std::string> rule_lhs_strings(const std::vector<RewriteRule> &rules)
    {
        std::vector<std::string> items;
        items.reserve(rules.size());
        for (const RewriteRule &r : rules)
            items.push_back(r.lhs.to_string());
        std::sort(items.begin(), items.end());
        return items;
    }

    void write_rule_analysis(std::ostream &os,
                             const std::vector<RewriteRule> &rules,
                             const std::vector<std::size_t> *topo,
                             const std::vector<RewriteRule> *composed,
                             const PolyDecls &d)
    {
        (void)d;
        const std::vector<std::string> lhs_keys = rule_lhs_strings(rules);
        std::unordered_map<std::string, std::string> lhs_by_key;
        for (const RewriteRule &r : rules)
            lhs_by_key.emplace(variable_key(r.lhs), r.lhs.to_string());

        os << "assignment LHS set: " << format_raw_set(lhs_keys) << "\n\n";

        os << "assignment dependencies:\n";
        if (rules.empty())
            os << "(none)\n";
        else
        {
            for (const RewriteRule &r : rules)
            {
                std::vector<std::string> deps;
                for (const std::string &v : collect_sorted_vars(r.rhs))
                {
                    auto it = lhs_by_key.find(v);
                    if (it != lhs_by_key.end())
                        deps.push_back(it->second);
                }
                os << r.lhs.to_string() << " -> " << format_raw_set(deps) << "\n";
            }
        }
        os << "\n";

        os << "topological order:\n";
        if (!topo)
            os << "rejected: circular dependency\n";
        else if (topo->empty())
            os << "(none)\n";
        else
            for (std::size_t idx : *topo)
                os << rules[idx].lhs.to_string() << "\n";
        os << "\n";

        os << "composed env:\n";
        if (!composed)
            os << "(not composed)\n";
        else
            write_rule_list(os, *composed, d);
        os << "\n";
    }

    void write_residual_list(std::ostream &os,
                             const std::vector<Extraction::Residual> &residuals,
                             const PolyDecls &d)
    {
        (void)d;
        if (residuals.empty())
        {
            os << "(none)\n";
            return;
        }
        for (std::size_t i = 0; i < residuals.size(); ++i)
        {
            os << "[" << i << "] " << residuals[i].polynomial.to_string();
            if (!residuals[i].reason.empty())
                os << "    reason: " << residuals[i].reason;
            os << "\n";
        }
    }

    void write_round_prefix(std::ostream &os,
                            std::size_t round,
                            const Extraction &ex,
                            const PolyDecls &d)
    {
        os << "[DAG round " << round << "]\n";
        os << "input formulas: " << ex.input_count << "\n\n";
        for (std::size_t i = 0; i < ex.input_formulas.size(); ++i)
            os << "[" << i << "] " << ex.input_formulas[i].to_string() << "\n";
        os << "\n";
        os << "assignments extracted: " << ex.rules.size() << "\n\n";
        os << "assignments:\n";
        write_rule_list(os, ex.rules, d);
        os << "\n";
        os << "residuals kept in this round: " << ex.residuals.size() << "\n\n";
        os << "residuals:\n";
        write_residual_list(os, ex.residuals, d);
        os << "\n";
    }

    void write_residual_rewrite_log(std::ostream &os,
                                    const std::vector<Extraction::Residual> &originals,
                                    const std::vector<expr> &rewritten,
                                    const std::vector<std::string> &drop_reasons,
                                    const PolyDecls &d)
    {
        (void)d;
        os << "residual rewrite:\n";
        if (originals.empty())
        {
            os << "(none)\n\n";
            return;
        }
        for (std::size_t i = 0; i < originals.size(); ++i)
        {
            os << "[" << i << "] " << originals[i].polynomial.to_string() << "\n";
            if (i < rewritten.size() && expr_key(originals[i].polynomial) == expr_key(rewritten[i]))
                os << "==> unchanged";
            else if (i < rewritten.size())
                os << "==> " << rewritten[i].to_string();
            if (i < drop_reasons.size() && !drop_reasons[i].empty())
                os << "    reason: " << drop_reasons[i];
            os << "\n\n";
        }
    }

    void write_final_residuals(std::ostream &os, const std::vector<expr> &residuals, const PolyDecls &d)
    {
        (void)d;
        os << "final residuals:\n";
        if (residuals.empty())
        {
            os << "(none)\n\n";
            return;
        }
        for (std::size_t i = 0; i < residuals.size(); ++i)
            os << "[" << i << "] " << residuals[i].to_string() << "\n";
        os << "\n";
    }

    AssertionWorkItem rewrite_item_to_work_item(const RewriteItem &item)
    {
        return AssertionWorkItem{item.formula, collect_vars(item.formula), item.poly_view, item.rule_candidate};
    }

    void update_env_dependents_on_new_rule(std::vector<RewriteRule> &env,
                                           const RewriteRule &new_rule,
                                           const PolyDecls &d)
    {
        if (!is_poly_variable(new_rule.lhs))
            return;
        const std::string new_lhs = variable_key(new_rule.lhs);
        for (RewriteRule &old : env)
        {
            if (!std::binary_search(old.rhs_dependencies.begin(), old.rhs_dependencies.end(), new_lhs))
                continue;
            bool changed = false;
            old.rhs = simplify_poly(substitute_one_rec(old.rhs, new_rule, d, changed), d);
            if (changed)
                old.rhs_dependencies = collect_sorted_vars(old.rhs);
        }
    }

    std::vector<expr> residual_polys_from_work_items(const std::vector<AssertionWorkItem> &residuals,
                                                     const std::vector<expr> &moduli,
                                                     const PolyDecls &d,
                                                     const RewriteOptions &options,
                                                     RewriteStats &stats)
    {
        std::vector<expr> others;
        others.reserve(residuals.size());
        for (const AssertionWorkItem &r : residuals)
        {
            if (!r.poly_view)
                continue;
            expr p = moduli.empty() ? *r.poly_view
                                    : normalize_poly_under_moduli(*r.poly_view, moduli, d, options, stats);
            others.push_back(p);
        }
        return others;
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

    std::vector<RewriteItem> functional_worklist_rewrite(std::vector<RewriteItem> current,
                                                        const std::vector<expr> &moduli,
                                                        const PolyDecls &d,
                                                        const RewriteOptions &options,
                                                        AssertionRewriteResult &res,
                                                        AssertionRewriteTiming *timing = nullptr)
    {
        std::deque<AssertionWorkItem> stack;
        for (const RewriteItem &item : current)
            stack.push_back(rewrite_item_to_work_item(item));

        std::vector<AssertionWorkItem> residuals;
        std::vector<RewriteRule> env;
        std::unordered_map<std::string, std::size_t> env_index;

        const std::size_t iteration_limit =
            options.max_rounds * std::max<std::size_t>(1, current.size() + 1);
        std::size_t iterations = 0;

        while (!stack.empty() && iterations++ < iteration_limit)
        {
            AssertionWorkItem item = std::move(stack.front());
            stack.pop_front();

            RewriteEnv rewrite_env(env, d, options);
            auto rewrite_t0 = std::chrono::steady_clock::now();
            expr rw = rewrite_assertion(item.formula, rewrite_env, options, res.stats);
            if (timing)
            {
                timing->residual_rewrite += std::chrono::steady_clock::now() - rewrite_t0;
                ++timing->residual_rewrite_calls;
            }
            if (is_true_expr(rw))
                continue;

            item.formula = rw;
            item.vars = collect_vars(rw);
            if (item.rule_candidate && is_eqP_atom(rw))
            {
                expr p = simplify_poly(mk_psub(d, rw.arg(0), rw.arg(1)), d);
                if (!moduli.empty())
                    p = normalize_poly_under_moduli(p, moduli, d, options, res.stats);
                item.poly_view = p;
            }
            else
                item.poly_view = std::nullopt;

            if (item.rule_candidate && item.poly_view)
            {
                const std::vector<expr> others =
                    residual_polys_from_work_items(residuals, moduli, d, options, res.stats);
                GeneratorInfo info(item.formula, *item.poly_view, false, true,
                                   "assert-wl-" + std::to_string(iterations), 0);
                auto pat = extract_one_assignment(info, others, moduli, d, options, res.stats,
                                                res.diagnostics);
                if (pat && !contains_expr(pat->rule.rhs, pat->rule.lhs))
                {
                    auto existing = env_index.find(pat->lhs_key);
                    if (existing != env_index.end())
                    {
                        residuals.push_back(std::move(item));
                    }
                    else
                    {
                        RewriteRule new_rule = pat->rule;
                        update_env_dependents_on_new_rule(env, new_rule, d);
                        env_index[pat->lhs_key] = env.size();
                        env.push_back(new_rule);
                        ++res.stats.rules_extracted;

                        const std::string new_lhs_key = variable_key(new_rule.lhs);
                        std::vector<AssertionWorkItem> keep;
                        keep.reserve(residuals.size());
                        for (AssertionWorkItem &r : residuals)
                        {
                            if (r.vars.count(new_lhs_key))
                                stack.push_back(std::move(r));
                            else
                                keep.push_back(std::move(r));
                        }
                        residuals.swap(keep);
                    }
                }
                else
                    residuals.push_back(std::move(item));
            }
            else
                residuals.push_back(std::move(item));
        }

        while (!stack.empty())
        {
            AssertionWorkItem item = std::move(stack.front());
            stack.pop_front();
            RewriteEnv rewrite_env(env, d, options);
            expr rw = rewrite_assertion(item.formula, rewrite_env, options, res.stats);
            if (!is_true_expr(rw))
                residuals.push_back(AssertionWorkItem{rw, collect_vars(rw), std::nullopt, false});
        }

        std::vector<expr> formulas;
        formulas.reserve(residuals.size());
        for (const AssertionWorkItem &r : residuals)
            formulas.push_back(r.formula);

        res.rules_used.insert(res.rules_used.end(), env.begin(), env.end());
        res.used_worklist_rewrite = true;

        auto make_t0 = std::chrono::steady_clock::now();
        std::vector<RewriteItem> out = make_rewrite_items(formulas, d);
        if (timing)
            timing->make_items += std::chrono::steady_clock::now() - make_t0;
        return out;
    }

    AssertionRewriteResult try_dag_rewrite(const std::vector<expr> &input_asserts,
                                                      const PolyDecls &d,
                                                      const RewriteOptions &options,
                                                      AssertionRewriteTiming *timing = nullptr)
    {
        AssertionRewriteResult res;
        auto make_t0 = std::chrono::steady_clock::now();
        std::vector<RewriteItem> current = make_rewrite_items(input_asserts, d);
        if (timing)
            timing->make_items += std::chrono::steady_clock::now() - make_t0;
        const std::vector<expr> moduli;

        for (std::size_t round = 0; round < options.max_rounds; ++round)
        {
            if (timing)
            {
                ++timing->rounds;
                timing->items_seen += current.size();
            }
            auto extract_t0 = std::chrono::steady_clock::now();
            Extraction ex = extract_assertion_item_assignments(current, moduli, d, options,
                                                               res.stats, res.diagnostics,
                                                               "assert-r" + std::to_string(round));
            if (timing)
                timing->extract += std::chrono::steady_clock::now() - extract_t0;
            if (ex.rules.empty())
            {
                std::vector<expr> simplified;
                simplified.reserve(current.size());
                std::vector<Extraction::Residual> originals;
                originals.reserve(current.size());
                std::vector<std::string> drop_reasons;
                drop_reasons.reserve(current.size());
                RewriteEnv empty_env(ex.rules, d, options);
                auto rewrite_t0 = std::chrono::steady_clock::now();
                for (std::size_t i = 0; i < current.size(); ++i)
                {
                    originals.emplace_back(current[i].formula, "", i);
                    expr rw = rewrite_assertion(current[i].formula, empty_env, options, res.stats);
                    simplified.push_back(rw);
                    drop_reasons.push_back(is_true_expr(rw) ? "dropped because true" : "");
                }
                if (timing)
                {
                    timing->residual_rewrite += std::chrono::steady_clock::now() - rewrite_t0;
                    timing->residual_rewrite_calls += current.size();
                }
                make_t0 = std::chrono::steady_clock::now();
                current = make_rewrite_items(simplified, d);
                if (timing)
                    timing->make_items += std::chrono::steady_clock::now() - make_t0;
                if (options.rewrite_log)
                {
                    const std::vector<std::size_t> empty_topo;
                    const std::vector<RewriteRule> empty_rules;
                    write_round_prefix(*options.rewrite_log, round + 1, ex, d);
                    write_rule_analysis(*options.rewrite_log, ex.rules, &empty_topo, &empty_rules, d);
                    write_residual_rewrite_log(*options.rewrite_log, originals, simplified, drop_reasons, d);
                    write_final_residuals(*options.rewrite_log, formulas_from_items(current), d);
                }
                break;
            }

            std::vector<std::size_t> sorted;
            try
            {
                auto topo_t0 = std::chrono::steady_clock::now();
                sorted = topo_sort_rules(ex.rules);
                if (timing)
                    timing->topo_sort += std::chrono::steady_clock::now() - topo_t0;
            }
            catch (const CircularDependency &)
            {
                current = functional_worklist_rewrite(std::move(current), moduli, d, options, res, timing);
                break;
            }

            std::vector<RewriteRule> env;
            try
            {
                auto compose_t0 = std::chrono::steady_clock::now();
                env = compose_rules(ex.rules, sorted, d, options);
                if (timing)
                    timing->compose += std::chrono::steady_clock::now() - compose_t0;
            }
            catch (const CircularDependency &)
            {
                current = functional_worklist_rewrite(std::move(current), moduli, d, options, res, timing);
                break;
            }

            auto env_t0 = std::chrono::steady_clock::now();
            RewriteEnv rewrite_env(env, d, options);
            if (timing)
                timing->build_env += std::chrono::steady_clock::now() - env_t0;
            ++res.dag_rounds;
            res.rules_used.insert(res.rules_used.end(), env.begin(), env.end());

            std::unordered_set<std::size_t> consumed(ex.consumed_input_indices.begin(),
                                                     ex.consumed_input_indices.end());
            std::vector<expr> rewritten;
            rewritten.reserve(current.size());
            std::vector<expr> log_rewritten;
            std::vector<Extraction::Residual> log_originals;
            std::vector<std::string> drop_reasons;
            auto rewrite_t0 = std::chrono::steady_clock::now();
            for (std::size_t i = 0; i < current.size(); ++i)
            {
                if (consumed.count(i))
                    continue;
                if (timing)
                    ++timing->residual_rewrite_calls;
                log_originals.emplace_back(current[i].formula, "", i);
                expr rw = rewrite_assertion(current[i].formula, rewrite_env, options, res.stats);
                log_rewritten.push_back(rw);
                drop_reasons.push_back(is_true_expr(rw) ? "dropped because true" : "");
                if (!is_true_expr(rw))
                    rewritten.push_back(rw);
            }
            if (timing)
                timing->residual_rewrite += std::chrono::steady_clock::now() - rewrite_t0;

            if (options.rewrite_log)
            {
                write_round_prefix(*options.rewrite_log, round + 1, ex, d);
                write_rule_analysis(*options.rewrite_log, ex.rules, &sorted, &env, d);
                write_residual_rewrite_log(*options.rewrite_log, log_originals, log_rewritten, drop_reasons, d);
            }
            make_t0 = std::chrono::steady_clock::now();
            current = make_rewrite_items(rewritten, d);
            if (timing)
                timing->make_items += std::chrono::steady_clock::now() - make_t0;
        }

        auto collect_t0 = std::chrono::steady_clock::now();
        res.residual_assertions = formulas_from_items(current);
        if (timing)
            timing->final_collect += std::chrono::steady_clock::now() - collect_t0;
        return res;
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

RewriteResult run_rewriting_pipeline(z3::context &ctx,
                                     const std::vector<z3::expr> &input_asserts,
                                     const RewriteOptions &option,
                                     util::Logger &log)
{
    const auto rewrite_t0 = std::chrono::steady_clock::now();
    std::chrono::nanoseconds pre_scan_time{0};
    std::chrono::nanoseconds collect_decls_time{0};
    std::chrono::nanoseconds assertion_rewrite_time{0};
    std::chrono::nanoseconds legacy_rule_time{0};
    std::chrono::nanoseconds post_scan_time{0};
    std::chrono::nanoseconds substitution_log_time{0};
    expr zero = ctx.int_val(0);
    RewriteResult out(zero);
    out.asserts = input_asserts;

    auto phase_t0 = std::chrono::steady_clock::now();
    std::vector<expr> eqps_before;
    std::vector<expr> asserted_eqps_before;
    std::vector<expr> eqmods_before;
    for (const expr &a : input_asserts)
    {
        collect_eqP_rec(a, eqps_before);
        collect_eqmodP1_rec(a, eqmods_before);
    }
    collect_asserted_eqP(input_asserts, asserted_eqps_before);
    out.rewrite_atoms_before = (int)(eqps_before.size() + eqmods_before.size());
    out.unique_vars_before = count_rewrite_vars(input_asserts);
    pre_scan_time = std::chrono::steady_clock::now() - phase_t0;

    if (!option.enable_rewriting)
    {
        out.residual_assertions = input_asserts;
        out.rewrite_atoms_after = out.rewrite_atoms_before;
        out.unique_vars_after = out.unique_vars_before;
        const auto rewrite_t1 = std::chrono::steady_clock::now();
        LOG_INFO(log, "rewrite", "[rewrite] mode: disabled"
                                    " time=" +
                                      util::fmt_duration(rewrite_t1 - rewrite_t0));
        return out;
    }

    std::vector<expr> roots = input_asserts;
    phase_t0 = std::chrono::steady_clock::now();
    PolyDecls d = collect_decls(roots);
    collect_decls_time = std::chrono::steady_clock::now() - phase_t0;
    if (!d.pconst)
    {
        out.residual_assertions = input_asserts;
        out.rewrite_atoms_after = out.rewrite_atoms_before;
        out.unique_vars_after = out.unique_vars_before;
        const auto rewrite_t1 = std::chrono::steady_clock::now();
        LOG_WARN(log, "rewrite", "[rewrite] no PConst constructor found; skipping rewriting"
                                  " time=" +
                                    util::fmt_duration(rewrite_t1 - rewrite_t0));
        return out;
    }
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
    ScopedSimplifyMemo simplify_scope(options);
    expr poly_zero = mk_pconst_mpz(d, ctx, 0);

    AssertionRewriteTiming assertion_timing;
    phase_t0 = std::chrono::steady_clock::now();
    AssertionRewriteResult unified = try_dag_rewrite(input_asserts, d, options, &assertion_timing);
    assertion_rewrite_time = std::chrono::steady_clock::now() - phase_t0;

    out.residual_assertions = unified.residual_assertions;
    out.asserts = unified.residual_assertions;
    out.rewritten_target = poly_zero;
    out.rules_used = unified.rules_used;
    out.used_worklist_rewrite = unified.used_worklist_rewrite;
    out.dag_rounds = unified.dag_rounds;
    out.stats = unified.stats;
    out.diagnostics = unified.diagnostics;
    if (unified.used_worklist_rewrite)
        out.diagnostics.push_back("worklist rewrite used");

    phase_t0 = std::chrono::steady_clock::now();
    for (const RewriteRule &r : unified.rules_used)
    {
        const std::string key = variable_key(r.lhs);
        out.rewrite_rules[key] = to_legacy_rule(r, d);
    }
    legacy_rule_time = std::chrono::steady_clock::now() - phase_t0;

    phase_t0 = std::chrono::steady_clock::now();
    std::vector<expr> eqps_after;
    std::vector<expr> eqmods_after;
    for (const expr &a : out.asserts)
    {
        collect_eqP_rec(a, eqps_after);
        collect_eqmodP1_rec(a, eqmods_after);
    }
    out.rewrite_atoms_after = (int)(eqps_after.size() + eqmods_after.size());
    out.unique_vars_after = count_rewrite_vars(out.asserts);
    post_scan_time = std::chrono::steady_clock::now() - phase_t0;

    const auto rewrite_t1 = std::chrono::steady_clock::now();
    std::ostringstream summary;
    summary << "[rewrite] input_rewrite_atoms=" << out.rewrite_atoms_before
            << " asserted_eqP=" << asserted_eqps_before.size()
            << " assignments=" << out.rules_used.size()
            << " residual_assertions=" << out.residual_assertions.size()
            << " dag_rounds=" << out.dag_rounds
            << " worklist=" << (out.used_worklist_rewrite ? "yes" : "no")
            << " singular_nf=" << out.stats.singular_nf_checks
            << " singular_zero=" << out.stats.singular_zero_reductions
            << " singular_failures=" << out.stats.singular_failures
            << " time=" << util::fmt_duration(rewrite_t1 - rewrite_t0);
    LOG_INFO(log, "rewrite", summary.str());

    std::ostringstream timing_summary;
    timing_summary << "[rewrite timing] pre_scan=" << util::fmt_duration(pre_scan_time)
                   << " collect_decls=" << util::fmt_duration(collect_decls_time)
                   << " assertion_total=" << util::fmt_duration(assertion_rewrite_time)
                   << " legacy_rules=" << util::fmt_duration(legacy_rule_time)
                   << " post_scan=" << util::fmt_duration(post_scan_time)
                   << " rounds=" << assertion_timing.rounds
                   << " items_seen=" << assertion_timing.items_seen
                   << " residual_rewrite_calls=" << assertion_timing.residual_rewrite_calls
                   << "\n  assertion_detail:"
                   << " make_items=" << util::fmt_duration(assertion_timing.make_items)
                   << " extract=" << util::fmt_duration(assertion_timing.extract)
                   << " topo=" << util::fmt_duration(assertion_timing.topo_sort)
                   << " compose=" << util::fmt_duration(assertion_timing.compose)
                   << " build_env=" << util::fmt_duration(assertion_timing.build_env)
                   << " residual_rewrite=" << util::fmt_duration(assertion_timing.residual_rewrite)
                   << " final_collect=" << util::fmt_duration(assertion_timing.final_collect);
    LOG_INFO(log, "rewrite", timing_summary.str());

    if (!out.rewrite_rules.empty())
    {
        phase_t0 = std::chrono::steady_clock::now();
        std::vector<std::string> lines;
        for (const auto &kv : out.rewrite_rules)
            lines.push_back("    " + pretty_rewrite_atom_name(kv.first) + " -> " + rule_rhs_pretty(kv.second) +
                            " [" + kv.second.source_label + "]");
        std::sort(lines.begin(), lines.end());
        std::ostringstream oss;
        oss << "[rewrite] substitutions (" << lines.size() << "):\n";
        for (const auto &line : lines)
            oss << line << "\n";
        if (!out.diagnostics.empty())
        {
            oss << "  diagnostics (" << out.diagnostics.size() << "):\n";
            for (const std::string &sk : out.diagnostics)
                oss << "    " << sk << "\n";
        }
        substitution_log_time = std::chrono::steady_clock::now() - phase_t0;
        LOG_INFO(log, "rewrite", oss.str());
        LOG_INFO(log, "rewrite", "[rewrite timing] substitution_log_build=" +
                                      util::fmt_duration(substitution_log_time));
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

    bool pipeline_selftest(const char *name,
                           const char *smt_body,
                           const std::function<bool(context &, const std::vector<expr> &, const RewriteResult &)> &pred,
                           RewriteOptions opts = {})
    {
        std::cout << "[selftest] " << name << "\n";
        context ctx;
        auto asserts = parse_assertions(ctx, smt_body);
        opts.use_singular_normalization = false;
        util::Logger log;
        log.set_global(util::LogLevel::Error);
        RewriteResult rr = run_rewriting_pipeline(ctx, asserts, opts, log);
        bool ok = pred(ctx, asserts, rr);
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

    run(pipeline_selftest("top-level conjunct eqP extracts rules",
                          "(declare-const x Int)(declare-const y Int)"
                          "(assert (and (eqP (PConst x) (PConst 1))"
                          "             (eqP (PConst y) (PConst x))))",
                          [](context &, const std::vector<expr> &, const RewriteResult &rr)
                          {
                              bool ok = check(rr.rules_used.size() == 2,
                                              "top-level conjunct eqP was not used for rewriting");
                              ok &= check(rr.asserts.empty(),
                                          "top-level conjunct eqP assertion was not rewritten away");
                              return ok;
                          }));

    run(pipeline_selftest("nested eqP is not an unconditional rule source",
                          "(declare-const x Int)(declare-const guard Bool)"
                          "(assert (or guard (eqP (PConst x) (PConst 0))))",
                          [](context &, const std::vector<expr> &input, const RewriteResult &rr)
                          {
                              bool ok = check(rr.rules_used.empty(),
                                              "nested eqP was used as an unconditional rewrite");
                              ok &= check(rr.asserts.size() == input.size(),
                                          "nested eqP assertion was rewritten away");
                              return ok;
                          }));

    run(pipeline_selftest("top-level rule rewrites nested eqP residual",
                          "(declare-const x Int)"
                          "(assert (eqP (PConst x) (PConst 1)))"
                          "(assert (not (eqP (PConst x) (PConst 2))))",
                          [](context &ctx, const std::vector<expr> &input, const RewriteResult &rr)
                          {
                              PolyDecls d = collect_decls(input);
                              std::vector<expr> eqps;
                              for (const expr &a : rr.asserts)
                                  collect_eqP_rec(a, eqps);
                              bool ok = check(rr.rules_used.size() == 1,
                                              "nested eqP was used as a rule source");
                              ok &= check(rr.asserts.size() == 1,
                                          "nested eqP residual was dropped unexpectedly");
                              ok &= check(rr.residual_assertions.size() == rr.asserts.size(),
                                          "residual_assertions no longer mirrors final assertions");
                              if (ok)
                                  ok &= check(eqps.size() == 1 &&
                                                  equivalent_for_test(eqps[0].arg(0), mk_pconst_mpz(d, ctx, 1), d),
                                              "nested eqP residual was not rewritten by top-level rule");
                              return ok;
                          }));

    run(pipeline_selftest("cyclic assertions use worklist rewrite",
                          "(declare-const x Int)(declare-const y Int)"
                          "(assert (eqP (PConst x) (PAdd (PConst y) (PConst 1))))"
                          "(assert (eqP (PConst y) (PAdd (PConst x) (PConst 1))))",
                          [](context &, const std::vector<expr> &input, const RewriteResult &rr)
                          {
                              bool ok = check(rr.used_worklist_rewrite, "worklist rewrite not used");
                              ok &= check(!rr.rules_used.empty(), "cyclic rewrite produced no rules");
                              ok &= check(rr.rules_used.size() < input.size(),
                                          "cyclic rewrite did not consume any eqP as rules");
                              return ok;
                          }));

    run(pipeline_selftest("cyclic worklist keeps non-poly residual",
                          "(declare-const x Int)(declare-const y Int)"
                          "(declare-const a Int)(declare-const b Int)"
                          "(assert (eqP (PConst x) (PAdd (PConst y) (PConst 1))))"
                          "(assert (eqP (PConst y) (PAdd (PConst x) (PConst 1))))"
                          "(assert (= a b))",
                          [](context &, const std::vector<expr> &input, const RewriteResult &rr)
                          {
                              bool has_int_equality = false;
                              for (const expr &a : rr.residual_assertions)
                                  has_int_equality =
                                      has_int_equality || (a.is_app() && a.decl().name().str() == "=");
                              bool ok = check(rr.used_worklist_rewrite, "worklist rewrite not used");
                              ok &= check(!rr.asserts.empty(), "all assertions were dropped after cyclic worklist");
                              ok &= check(has_int_equality, "non-poly equality missing after cyclic worklist");
                              ok &= check(rr.asserts.size() < input.size(),
                                          "cyclic worklist did not eliminate any assertions");
                              return ok;
                          }));

    run(pipeline_selftest("non-poly assertion remains in residual assertions",
                          "(declare-const x Int)(declare-const a Int)(declare-const b Int)"
                          "(assert (and (eqP (PConst x) (PConst 1)) (= a b)))",
                          [](context &, const std::vector<expr> &, const RewriteResult &rr)
                          {
                              bool has_int_equality = false;
                              for (const expr &a : rr.residual_assertions)
                                  has_int_equality =
                                      has_int_equality || (a.is_app() && a.decl().name().str() == "=");
                              bool ok = check(rr.rules_used.size() == 1, "top-level eqP did not produce a rule");
                              ok &= check(rr.asserts.size() == 1,
                                          "non-poly assertion was not the only residual assertion");
                              ok &= check(rr.residual_assertions.size() == rr.asserts.size(),
                                          "residual_assertions no longer carries final SMT assertions");
                              ok &= check(has_int_equality,
                                          "non-poly equality was not preserved in residual_assertions");
                              return ok;
                          }));

    run(pipeline_selftest("eqmodP1 variables rewrite by default",
                          "(declare-const x Int)(declare-const y Int)"
                          "(assert (eqP (PConst x) (PConst 1)))"
                          "(assert (not (eqmodP1 (PConst x) (PConst y) (PConst 7))))",
                          [](context &ctx, const std::vector<expr> &input, const RewriteResult &rr)
                          {
                              std::vector<expr> ems;
                              for (const expr &a : rr.asserts)
                                  collect_eqmodP1_rec(a, ems);
                              PolyDecls d = collect_decls(rr.asserts);
                              bool ok = check(ems.size() == 1, "rewritten eqmodP1 atom missing");
                              if (ok)
                                  ok &= check(equivalent_for_test(ems[0].arg(0), mk_pconst_mpz(d, ctx, 1), d),
                                              "eqmodP1 lhs was not rewritten from asserted eqP");

                              RewriteOptions preserve;
                              preserve.use_singular_normalization = false;
                              preserve.preserve_eqmodp1_vars = true;
                              util::Logger log;
                              log.set_global(util::LogLevel::Error);
                              RewriteResult kept =
                                  run_rewriting_pipeline(ctx, input, preserve, log);
                              bool kept_rule = false;
                              for (const RewriteRule &r : kept.rules_used)
                                  kept_rule = kept_rule || variable_key(r.lhs) == "x";
                              ok &= check(!kept_rule, "preserve mode still extracted eqmodP1 lhs rule");
                              return ok;
                          }));

    run(pipeline_selftest("eqmodP1 arguments rewrite by their own modulus",
                          "(declare-const x Int)(declare-const m Int)"
                          "(assert (eqmodP1 (PAdd (PConst x) (PMul (PConst 3) (PConst m))) (PConst x) (PConst m)))",
                          [](context &, const std::vector<expr> &, const RewriteResult &rr)
                          {
                              return check(rr.asserts.empty(),
                                           "eqmodP1 did not reduce to true after dropping modulus multiple");
                          }));

    run(pipeline_selftest("single affine eqP is fully rewritten",
                          "(declare-const x Int)(declare-const y Int)"
                          "(assert (eqP (PSub (PConst x) (PConst y)) (PConst 0)))",
                          [](context &, const std::vector<expr> &, const RewriteResult &rr)
                          {
                              bool ok = check(rr.rules_used.size() == 1, "expected one extracted rule");
                              ok &= check(rr.asserts.empty(), "affine eqP assertion was not rewritten away");
                              return ok;
                          }));


    std::cout << "\n[selftest] " << pass << "/" << total << " passed\n";
    return pass == total ? 0 : 2;
}
