#include "eqmod_engine.hpp"

#include <algorithm>
#include <array>
#include <cstring>
#include <sstream>
#include <stdexcept>

#include "util/singular_poly.hpp"

using namespace z3;
using namespace util::singular::lowering;
using util::singular::copy_poly_or_null;
using util::singular::delete_poly_if_nonnull;
using util::singular::num_from_si;
using util::singular::poly_add_owned;
using util::singular::poly_from_mpz;
using util::singular::poly_from_si;
using util::singular::poly_mul_clone;
using util::singular::poly_negate_owned;
using util::singular::poly_sub_product_clone;
using util::singular::poly_to_string;
using util::singular::ScopedPolyOwner;

namespace eqmod
{
P1Compiled::P1Compiled(const expr &atom_value,
                       const expr &lhs,
                       const expr &rhs,
                       const expr &modulus,
                       std::string quotient_name,
                       ring current_ring)
    : atom(atom_value), A(lhs), B(rhs), Mterm(modulus),
      u_name(std::move(quotient_name)), owner_ring(current_ring)
{
}

P1Compiled::~P1Compiled()
{
    if (owner_ring)
        destroy(*this, owner_ring);
}

P1Compiled::P1Compiled(P1Compiled &&other) noexcept
    : atom(std::move(other.atom)), A(std::move(other.A)),
      B(std::move(other.B)), Mterm(std::move(other.Mterm)),
      modulus_ok(other.modulus_ok),
      modulus_is_const(other.modulus_is_const),
      m_const(std::move(other.m_const)),
      M_poly(std::exchange(other.M_poly, nullptr)),
      D(std::exchange(other.D, nullptr)),
      u_name(std::move(other.u_name)),
      U_poly(std::exchange(other.U_poly, nullptr)),
      true_gen(std::exchange(other.true_gen, nullptr)),
      valid(other.valid),
      incomplete_reason(std::move(other.incomplete_reason)),
      propagated_truth(other.propagated_truth),
      propagated_truth_ants(std::move(other.propagated_truth_ants)),
      propagated_truth_eqs(std::move(other.propagated_truth_eqs)),
      owner_ring(std::exchange(other.owner_ring, nullptr))
{
}

P1Compiled &P1Compiled::operator=(P1Compiled &&other) noexcept
{
    if (this == &other)
        return *this;
    if (owner_ring)
        destroy(*this, owner_ring);
    atom = std::move(other.atom);
    A = std::move(other.A);
    B = std::move(other.B);
    Mterm = std::move(other.Mterm);
    modulus_ok = other.modulus_ok;
    modulus_is_const = other.modulus_is_const;
    m_const = std::move(other.m_const);
    M_poly = std::exchange(other.M_poly, nullptr);
    D = std::exchange(other.D, nullptr);
    u_name = std::move(other.u_name);
    U_poly = std::exchange(other.U_poly, nullptr);
    true_gen = std::exchange(other.true_gen, nullptr);
    valid = other.valid;
    incomplete_reason = std::move(other.incomplete_reason);
    propagated_truth = other.propagated_truth;
    propagated_truth_ants = std::move(other.propagated_truth_ants);
    propagated_truth_eqs = std::move(other.propagated_truth_eqs);
    owner_ring = std::exchange(other.owner_ring, nullptr);
    return *this;
}

NCompiled::NCompiled(const expr &atom_value,
                     const expr &lhs,
                     const expr &rhs,
                     unsigned family,
                     std::vector<expr> moduli,
                     std::vector<std::string> quotients,
                     ring current_ring)
    : atom(atom_value), A(lhs), B(rhs), arity(family),
      modulus_terms(std::move(moduli)),
      quotient_names(std::move(quotients)),
      M1term(modulus_terms.at(0)), M2term(modulus_terms.at(1)),
      u1_name(quotient_names.at(0)), u2_name(quotient_names.at(1)),
      owner_ring(current_ring)
{
}

NCompiled::~NCompiled()
{
    if (owner_ring)
        destroy(*this, owner_ring);
}

NCompiled::NCompiled(NCompiled &&other) noexcept
    : atom(std::move(other.atom)), A(std::move(other.A)),
      B(std::move(other.B)), arity(other.arity),
      modulus_terms(std::move(other.modulus_terms)),
      modulus_polys(std::exchange(other.modulus_polys, {})),
      quotient_names(std::move(other.quotient_names)),
      quotient_polys(std::exchange(other.quotient_polys, {})),
      M1term(std::move(other.M1term)), M2term(std::move(other.M2term)),
      D(std::exchange(other.D, nullptr)),
      M1_poly(other.M1_poly), M2_poly(other.M2_poly),
      u1_name(std::move(other.u1_name)), u2_name(std::move(other.u2_name)),
      U1_poly(other.U1_poly), U2_poly(other.U2_poly),
      true_gen(std::exchange(other.true_gen, nullptr)), valid(other.valid),
      incomplete_reason(std::move(other.incomplete_reason)),
      propagated_truth(other.propagated_truth),
      propagated_truth_ants(std::move(other.propagated_truth_ants)),
      propagated_truth_eqs(std::move(other.propagated_truth_eqs)),
      owner_ring(std::exchange(other.owner_ring, nullptr))
{
    other.M1_poly = other.M2_poly = nullptr;
    other.U1_poly = other.U2_poly = nullptr;
}

NCompiled &NCompiled::operator=(NCompiled &&other) noexcept
{
    if (this == &other)
        return *this;
    if (owner_ring)
        destroy(*this, owner_ring);
    atom = std::move(other.atom);
    A = std::move(other.A);
    B = std::move(other.B);
    arity = other.arity;
    modulus_terms = std::move(other.modulus_terms);
    modulus_polys = std::exchange(other.modulus_polys, {});
    quotient_names = std::move(other.quotient_names);
    quotient_polys = std::exchange(other.quotient_polys, {});
    M1term = std::move(other.M1term);
    M2term = std::move(other.M2term);
    D = std::exchange(other.D, nullptr);
    M1_poly = other.M1_poly;
    M2_poly = other.M2_poly;
    u1_name = std::move(other.u1_name);
    u2_name = std::move(other.u2_name);
    U1_poly = other.U1_poly;
    U2_poly = other.U2_poly;
    true_gen = std::exchange(other.true_gen, nullptr);
    valid = other.valid;
    incomplete_reason = std::move(other.incomplete_reason);
    propagated_truth = other.propagated_truth;
    propagated_truth_ants = std::move(other.propagated_truth_ants);
    propagated_truth_eqs = std::move(other.propagated_truth_eqs);
    owner_ring = std::exchange(other.owner_ring, nullptr);
    other.M1_poly = other.M2_poly = nullptr;
    other.U1_poly = other.U2_poly = nullptr;
    return *this;
}


EqmodEngine::EqmodEngine(
    const std::vector<std::string> &p1_qvars,
    const std::vector<std::vector<std::vector<std::string>>> &n_qvars,
    const std::vector<expr> &p1_atoms,
    const std::vector<std::vector<expr>> &n_atoms)
    : m_qvar_names(p1_qvars),
      m_eqmodn_qvar_names(n_qvars),
      m_eqmodp1_atoms(p1_atoms),
      m_eqmodn_atoms(n_atoms.empty()
                         ? std::vector<std::vector<expr>>(5)
                         : n_atoms),
      m_eqmodn_slots(5)
{
    if (m_eqmodn_atoms.size() < 5)
        m_eqmodn_atoms.resize(5);
    if (m_eqmodn_qvar_names.size() < 5)
        m_eqmodn_qvar_names.resize(5);
}

void EqmodEngine::bind_ring(ring current_ring)
{
    m_owned_ring = current_ring;
}

EqmodEngine::~EqmodEngine()
{
    release();
}

void EqmodEngine::release()
{
    if (!m_owned_ring)
        return;
    rChangeCurrRing(m_owned_ring);
    for (P1Compiled &atom : m_eqmodp)
        destroy(atom, m_owned_ring);
    for (NCompiled &atom : m_eqmodp2)
        destroy(atom, m_owned_ring);
    for (NCompiled &atom : m_eqmodp3)
        destroy(atom, m_owned_ring);
    for (NCompiled &atom : m_eqmodp4)
        destroy(atom, m_owned_ring);
    m_owned_ring = nullptr;
}

void EqmodEngine::reset_after_pop(bool live_equality_enabled)
{
    auto reset_family = [](auto &family)
    {
        for (auto &atom : family)
        {
            atom.propagated_truth = Z3_L_UNDEF;
            atom.propagated_truth_ants.clear();
            atom.propagated_truth_eqs.clear();
        }
    };
    reset_family(m_eqmodp);
    reset_family(m_eqmodp2);
    reset_family(m_eqmodp3);
    reset_family(m_eqmodp4);

    if (live_equality_enabled)
    {
        m_eqmod_true_lemma_replay_needed = true;
        return;
    }

    m_last_eqmod_true_lemma_true_count = static_cast<std::size_t>(-1);
    m_last_eqmod_true_lemma_p1_count = static_cast<std::size_t>(-1);
    m_last_eqmod_true_lemma_p2_count = static_cast<std::size_t>(-1);
    m_last_eqmod_true_lemma_p3_count = static_cast<std::size_t>(-1);
    m_last_eqmod_true_lemma_p4_count = static_cast<std::size_t>(-1);
    m_last_eqmod_true_lemma_eq_generator_epoch =
        static_cast<std::size_t>(-1);
}

void EqmodEngine::record_membership(unsigned family, bool member)
{
    if (family == 0 || family >= m_eqmod_membership_queries.size())
        return;
    ++m_eqmod_membership_queries[family];
    if (member)
        ++m_eqmod_membership_members[family];
    else
        ++m_eqmod_membership_nonmembers[family];
}

bool EqmodEngine::same_poly(poly lhs, poly rhs, ring current_ring)
{
    if (lhs == nullptr || rhs == nullptr)
        return lhs == rhs;
    return util::singular::poly_equal(lhs, rhs, current_ring);
}

std::string EqmodEngine::render_summary(bool final_validation_enabled) const
{
    const std::string status =
        !final_validation_enabled
            ? "disabled"
            : (m_semantic_validation_incomplete ? "incomplete" : "validated");
    std::ostringstream out;
    out << status;
    for (unsigned family = 1; family <= 4; ++family)
    {
        const std::size_t valid = family == 1 ? m_eqmodp.size() :
                                  family == 2 ? m_eqmodp2.size() :
                                  family == 3 ? m_eqmodp3.size() :
                                                m_eqmodp4.size();
        std::size_t qvars = 0;
        if (family == 1)
            qvars = m_qvar_names.size();
        else if (m_eqmodn_qvar_names.size() > family)
            for (const auto &names : m_eqmodn_qvar_names[family])
                qvars += names.size();
        out << "; P" << family
            << " collected=" << m_eqmod_collected_atoms[family]
            << " valid=" << valid
            << " invalid=" << m_eqmod_invalid_atoms[family]
            << " qvars=" << qvars
            << " membership=" << m_eqmod_membership_queries[family]
            << '(' << m_eqmod_membership_members[family] << " member/"
            << m_eqmod_membership_nonmembers[family] << " non-member)"
            << " true-cache="
            << m_eqmod_true_lemma_cache_hits_by_family[family] << " hit/"
            << m_eqmod_true_lemma_cache_misses_by_family[family] << " miss"
            << " refutation-cache="
            << m_eqmod_refutation_cache_hits_by_family[family] << " hit/"
            << m_eqmod_refutation_cache_misses_by_family[family] << " miss"
            << " refutation-conflicts="
            << m_eqmod_refutation_conflicts_by_family[family];
        if (family == 1)
            out << " prime-product=" << m_eqmod_p1_product_queries
                << " queries/" << m_eqmod_p1_product_members
                << " members/" << m_eqmod_p1_product_nonmembers
                << " non-members/" << m_eqmod_p1_product_cache_hits
                << " cache-hits/" << m_eqmod_p1_product_conflicts
                << " conflicts";
        out << " validation=" << m_eqmod_validation_checked[family]
            << " checked/" << m_eqmod_validation_matched[family]
            << " matched/" << m_eqmod_validation_conflicted[family]
            << " conflicted/" << m_eqmod_validation_skipped[family]
            << " skipped";
    }
    return out.str();
}

bool EqmodEngine::is_compiled(const expr &atom) const
{
    return m_compiled_eqmod_atoms.count((Z3_ast)atom) != 0;
}

void EqmodEngine::register_slot(const expr &atom, unsigned family,
                                std::size_t index)
{
    if (family == 1)
        m_eqmodp1_slots.emplace((Z3_ast)atom, index);
    else if (family >= 2 && family <= 4)
        m_eqmodn_slots.at(family).emplace((Z3_ast)atom, index);
    else
        throw std::runtime_error("invalid eqmod family for stable slot");
}

std::size_t EqmodEngine::require_slot(const expr &atom, unsigned family,
                                      const std::string &origin) const
{
    if (family == 1)
    {
        auto found = m_eqmodp1_slots.find((Z3_ast)atom);
        if (found == m_eqmodp1_slots.end() ||
            found->second >= m_qvar_names.size())
            throw std::runtime_error(
                origin + "(eqmodP1): missing stable preallocated qvar slot");
        return found->second;
    }

    if (family < 2 || family > 4 || m_eqmodn_slots.size() <= family ||
        m_eqmodn_qvar_names.size() <= family)
        throw std::runtime_error(origin + ": invalid eqmod family");
    auto found = m_eqmodn_slots[family].find((Z3_ast)atom);
    if (found == m_eqmodn_slots[family].end() ||
        found->second >= m_eqmodn_qvar_names[family].size())
        throw std::runtime_error(
            origin + "(eqmodP" + std::to_string(family) +
            "): missing stable preallocated qvar slot");
    return found->second;
}

bool EqmodEngine::lower_atom(
    const expr &atom,
    unsigned family,
    const std::string &label,
    const IndetEnv &indets,
    const std::vector<std::string> &indet_ring_names,
    RingEnv &ring_environment,
    const CoeffVarMap &coefficients,
    int coefficient_count,
    util::Logger &log)
{
    if (is_compiled(atom))
        return false;
    const std::size_t index = require_slot(atom, family, "created");

    bool valid = false;
    std::string incomplete_reason;
    if (family == 1)
    {
        P1Compiled lowered = compile_p1(
            atom, atom.arg(0), atom.arg(1), atom.arg(2), label, indets,
            indet_ring_names, ring_environment, coefficients,
            coefficient_count, m_qvar_names[index], log);
        valid = lowered.valid;
        incomplete_reason = lowered.incomplete_reason;
        if (valid)
            m_eqmodp.push_back(std::move(lowered));
    }
    else
    {
        NCompiled lowered = compile_n(
            atom, label, indets, indet_ring_names, ring_environment,
            coefficients, coefficient_count,
            m_eqmodn_qvar_names[family][index], log);
        valid = lowered.valid;
        incomplete_reason = lowered.incomplete_reason;
        auto &compiled = family == 2 ? m_eqmodp2 :
                         family == 3 ? m_eqmodp3 : m_eqmodp4;
        if (valid)
            compiled.push_back(std::move(lowered));
    }

    if (!valid)
    {
        ++m_eqmod_invalid_atoms.at(family);
        m_eqmod_incomplete_reasons.at(family).push_back(
            std::move(incomplete_reason));
        m_semantic_validation_incomplete = true;
    }
    m_compiled_eqmod_atoms.insert((Z3_ast)atom);
    return true;
}



} // namespace eqmod
