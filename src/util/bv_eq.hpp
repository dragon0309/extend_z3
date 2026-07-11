#pragma once

#include <z3++.h>

#include <algorithm>
#include <cstddef>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "util/logger.hpp"

namespace util::bveq
{

using namespace z3;

struct IndexedCandidate
{
    std::size_t lhs = 0;
    std::size_t rhs = 0;
    unsigned depth = 0;
    unsigned count = 0;
};

class CallbackCandidateCollector : public user_propagator_base
{
    std::vector<expr> m_terms;
    std::vector<std::pair<expr, expr>> m_candidates;
    std::vector<unsigned> m_candidate_depths;
    std::vector<unsigned> m_candidate_counts;
    std::unordered_map<std::string, std::size_t> m_seen;
    unsigned m_scope_depth = 0;

    static std::string pair_key(const expr &x, const expr &y)
    {
        const unsigned xid = Z3_get_ast_id((Z3_context)x.ctx(), (Z3_ast)x);
        const unsigned yid = Z3_get_ast_id((Z3_context)y.ctx(), (Z3_ast)y);
        return xid <= yid ? std::to_string(xid) + ":" + std::to_string(yid)
                          : std::to_string(yid) + ":" + std::to_string(xid);
    }

    void merge_candidate(const expr &x, const expr &y, unsigned depth, unsigned count)
    {
        const std::string key = pair_key(x, y);
        auto [it, inserted] = m_seen.emplace(key, m_candidates.size());
        if (inserted)
        {
            m_candidates.emplace_back(x, y);
            m_candidate_depths.push_back(depth);
            m_candidate_counts.push_back(count);
        }
        else
        {
            m_candidate_depths[it->second] =
                std::min(m_candidate_depths[it->second], depth);
            m_candidate_counts[it->second] += count;
        }
    }

    void initialize()
    {
        register_eq();
        for (const expr &term : m_terms)
            add(term);
    }

public:
    CallbackCandidateCollector(solver *s, const std::vector<expr> &terms)
        : user_propagator_base(s), m_terms(terms)
    {
        initialize();
    }

    CallbackCandidateCollector(context &c, const std::vector<expr> &terms)
        : user_propagator_base(c)
    {
        m_terms.reserve(terms.size());
        for (const expr &term : terms)
            m_terms.emplace_back(c, Z3_translate((Z3_context)term.ctx(),
                                                 (Z3_ast)term, (Z3_context)c));
        initialize();
    }

    const std::vector<std::pair<expr, expr>> &candidates() const
    {
        return m_candidates;
    }

    unsigned candidate_depth(std::size_t i) const
    {
        return m_candidate_depths[i];
    }

    unsigned candidate_count(std::size_t i) const
    {
        return m_candidate_counts[i];
    }

    void merge(const CallbackCandidateCollector &other)
    {
        for (std::size_t i = 0; i < other.m_candidates.size(); ++i)
        {
            const auto &[x, y] = other.m_candidates[i];
            merge_candidate(x, y, other.m_candidate_depths[i],
                            other.m_candidate_counts[i]);
        }
    }

    std::vector<IndexedCandidate> export_indexed_candidates() const
    {
        std::unordered_map<Z3_ast, std::size_t> term_indices;
        term_indices.reserve(m_terms.size());
        for (std::size_t i = 0; i < m_terms.size(); ++i)
            term_indices.emplace((Z3_ast)m_terms[i], i);

        std::vector<IndexedCandidate> out;
        out.reserve(m_candidates.size());
        for (std::size_t i = 0; i < m_candidates.size(); ++i)
        {
            const auto &[x, y] = m_candidates[i];
            auto xi = term_indices.find((Z3_ast)x);
            auto yi = term_indices.find((Z3_ast)y);
            if (xi == term_indices.end() || yi == term_indices.end())
                throw std::runtime_error("BV equality callback returned an unregistered term");
            out.push_back({xi->second, yi->second,
                           m_candidate_depths[i], m_candidate_counts[i]});
        }
        return out;
    }

    void merge_indexed_candidates(const std::vector<expr> &terms,
                                  const std::vector<IndexedCandidate> &candidates)
    {
        for (const IndexedCandidate &candidate : candidates)
        {
            if (candidate.lhs >= terms.size() || candidate.rhs >= terms.size())
                throw std::runtime_error("BV equality candidate term index is out of range");
            merge_candidate(terms[candidate.lhs], terms[candidate.rhs],
                            candidate.depth, candidate.count);
        }
    }

    void push() override { ++m_scope_depth; }
    void pop(unsigned num_scopes) override
    {
        m_scope_depth = num_scopes >= m_scope_depth ? 0 : m_scope_depth - num_scopes;
    }
    void final() override {}

    void eq(const expr &x, const expr &y) override
    {
        if (!x.is_const() || !y.is_const() ||
            !x.get_sort().is_bv() || !y.get_sort().is_bv() ||
            x.get_sort().bv_size() != y.get_sort().bv_size())
            return;
        merge_candidate(x, y, m_scope_depth, 1);
    }

    user_propagator_base *fresh(context &nctx) override
    {
        return new CallbackCandidateCollector(nctx, m_terms);
    }
};

struct Options
{
    bool parallel_candidates = false;
    bool all_bv_constants = false;
    bool enable_fallback = false;
    std::size_t validation_batch_size = 64;
    std::size_t seeded_candidate_solvers = 4;
};

struct ProvedEquality
{
    std::string conversion;
    std::string lhs_bv;
    std::string rhs_bv;
};

struct Result
{
    std::vector<ProvedEquality> equalities;
};

bool assertion_contains_poly(const z3::expr &e);
void collect_bv_constants(const z3::expr &e, std::unordered_set<Z3_ast> &out);

Result prove(z3::context &ctx,
             const std::vector<z3::expr> &assertions,
             const Options &options,
             util::Logger &log);

std::vector<z3::expr> inject_as_eqp(z3::context &ctx,
                                    const std::vector<z3::expr> &assertions,
                                    const Result &result,
                                    util::Logger &log);

} // namespace util::bveq
