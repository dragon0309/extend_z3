#include "util/pconst_purification.hpp"

#include "util/bv_to_int.hpp"

#include <cctype>
#include <cerrno>
#include <cstdlib>
#include <limits>
#include <unordered_map>
#include <utility>

namespace util::purify
{
namespace
{

// Z3_mk_fresh_const names the constants "pconst_term!0", "pconst_term!1", ...
constexpr const char *kConstantPrefix = "pconst_term";

bool is_pconst(const z3::expr &e)
{
    return e.is_app() && e.num_args() == 1 &&
           e.decl().name().str() == "PConst";
}

// The exponent test of expr_to_poly_anyring: an Int numeral that is not
// negative and fits in an unsigned long.
bool is_lowerable_exponent(const z3::expr &exponent)
{
    if (!exponent.is_numeral() || !exponent.get_sort().is_int())
        return false;
    const std::string text = Z3_get_numeral_string(exponent.ctx(), exponent);
    if (text.empty() || text[0] == '-')
        return false;
    errno = 0;
    char *end = nullptr;
    const unsigned long long value = std::strtoull(text.c_str(), &end, 10);
    return errno != ERANGE && end != nullptr && *end == '\0' &&
           value <= std::numeric_limits<unsigned long>::max();
}

class Purifier
{
public:
    explicit Purifier(z3::context &context) : m_context(context) {}

    // Rewrites the PConst arguments anywhere inside a formula or term.
    z3::expr rewrite(const z3::expr &e)
    {
        // Quantifiers and their bound variables stay as they are.
        if (!e.is_app())
            return e;
        if (const auto found = m_rewritten.find(e.id());
            found != m_rewritten.end())
            return found->second;

        z3::expr result = e;
        if (is_pconst(e) && e.arg(0).get_sort().is_int())
        {
            const z3::expr argument = purify_int(e.arg(0));
            if (!z3::eq(argument, e.arg(0)))
                result = e.decl()(argument);
        }
        else if (e.num_args() > 0)
        {
            z3::expr_vector arguments(m_context);
            bool changed = false;
            for (unsigned i = 0; i < e.num_args(); ++i)
            {
                const z3::expr argument = rewrite(e.arg(i));
                changed = changed || !z3::eq(argument, e.arg(i));
                arguments.push_back(argument);
            }
            if (changed)
                result = e.decl()(arguments);
        }
        m_rewritten.emplace(e.id(), result);
        return result;
    }

    std::vector<Replacement> take_replacements()
    {
        return std::move(m_replacements);
    }

private:
    // An Int term under a PConst: keeps the polynomial structure and names
    // everything else.
    z3::expr purify_int(const z3::expr &e)
    {
        if (!e.is_app())
            return e;
        if (const auto found = m_purified.find(e.id());
            found != m_purified.end())
            return found->second;

        z3::expr result = e;
        if (e.is_numeral() || e.num_args() == 0)
        {
            // A ring constant, or an Int constant the lowering maps to a ring
            // variable.
        }
        else if (is_bv_to_int_app(e))
        {
            // The conversion stays a ring variable, but its bit-vector
            // argument may hold another atom with a PConst, e.g. in an ite
            // condition.
            const z3::expr argument = rewrite(e.arg(0));
            if (!z3::eq(argument, e.arg(0)))
                result = e.decl()(argument);
        }
        else
        {
            switch (e.decl().decl_kind())
            {
            case Z3_OP_ADD:
            case Z3_OP_SUB:
            case Z3_OP_UMINUS:
            case Z3_OP_MUL:
                result = rebuild_with_purified_arguments(e);
                break;
            case Z3_OP_POWER:
                if (e.num_args() == 2 && is_lowerable_exponent(e.arg(1)))
                    result = e.decl()(purify_int(e.arg(0)), e.arg(1));
                else
                    result = name(e);
                break;
            default:
                result = name(e);
                break;
            }
        }
        m_purified.emplace(e.id(), result);
        return result;
    }

    z3::expr rebuild_with_purified_arguments(const z3::expr &e)
    {
        z3::expr_vector arguments(m_context);
        bool changed = false;
        for (unsigned i = 0; i < e.num_args(); ++i)
        {
            const z3::expr argument = purify_int(e.arg(i));
            changed = changed || !z3::eq(argument, e.arg(i));
            arguments.push_back(argument);
        }
        return changed ? e.decl()(arguments) : e;
    }

    // Replaces a non-polynomial subterm by a fresh constant c and records
    // (= c subterm). A PConst can sit inside the subterm itself (for example
    // in the condition of an ite), so the subterm is rewritten first.
    z3::expr name(const z3::expr &e)
    {
        const z3::expr term = rewrite(e);
        const z3::expr constant(
            m_context, Z3_mk_fresh_const(m_context, kConstantPrefix,
                                         m_context.int_sort()));
        m_replacements.push_back({constant, term});
        return constant;
    }

    z3::context &m_context;
    std::unordered_map<unsigned, z3::expr> m_rewritten; // by AST id
    std::unordered_map<unsigned, z3::expr> m_purified;  // by AST id
    std::vector<Replacement> m_replacements;
};

} // namespace

std::vector<Replacement> purify_pconst_arguments(
    z3::context &context, std::vector<z3::expr> &assertions)
{
    Purifier purifier(context);
    for (z3::expr &assertion : assertions)
        assertion = purifier.rewrite(assertion);

    std::vector<Replacement> replacements = purifier.take_replacements();
    for (const Replacement &replacement : replacements)
        assertions.push_back(replacement.constant == replacement.term);
    return replacements;
}

bool is_purification_constant_name(const std::string &name)
{
    const std::string prefix = std::string(kConstantPrefix) + "!";
    if (name.size() <= prefix.size() || name.compare(0, prefix.size(), prefix) != 0)
        return false;
    for (std::size_t i = prefix.size(); i < name.size(); ++i)
    {
        if (!std::isdigit(static_cast<unsigned char>(name[i])))
            return false;
    }
    return true;
}

} // namespace util::purify
