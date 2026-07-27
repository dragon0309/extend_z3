#pragma once

#include <z3++.h>

#include <chrono>
#include <cstddef>
#include <memory>
#include <string>
#include <utility>
#include <vector>

namespace util
{
class Logger;
}

namespace util::eqpartition
{

enum class Status
{
    Complete,
    Unknown,
    Error
};

struct Options
{
    // Zero means no timeout. A non-zero timeout makes Unknown a possible
    // result and therefore cannot provide a completeness guarantee.
    unsigned timeout_ms = 0;
    bool start_async = true;
};

struct Statistics
{
    std::size_t terms = 0;
    std::size_t initial_blocks = 0;
    std::size_t final_blocks = 0;
    std::size_t checks = 0;
    std::size_t sat_checks = 0;
    std::size_t unsat_checks = 0;
    std::size_t refinements = 0;
    std::size_t blocks_split = 0;
    std::size_t splitter_edges = 0;
    std::size_t max_splitter_edges = 0;
    std::size_t parallel_rounds = 0;
    std::size_t max_parallel_queries = 0;
    std::size_t final_validation_checks = 0;
    std::size_t equality_classes = 0;
    std::size_t proof_edges = 0;
    std::size_t implied_pairs = 0;
    std::chrono::nanoseconds check_time{0};
    std::chrono::nanoseconds final_validation_time{0};
    std::chrono::nanoseconds elapsed{0};
};

struct Result
{
    Status status = Status::Error;
    // True only when the initial plain constraints check returned UNSAT.
    // This is distinct from the final splitter check returning UNSAT.
    bool constraints_unsat = false;
    // Each block is one complete implied-equality class when status is
    // Complete. Singleton blocks are retained so coverage is auditable.
    std::vector<std::vector<std::size_t>> classes;
    // A spanning forest for the non-singleton classes. These equalities are
    // sufficient for propagation and GB generators; all class pairs follow by
    // transitivity.
    std::vector<std::pair<std::size_t, std::size_t>> proof_edges;
    Statistics statistics;
    std::string diagnostic;
};

// Computes all equalities implied by constraints among a fixed finite term
// universe using SMT-based partition refinement (Berdine/Bjoerner, IJCAR 2014).
// The source context is translated into an owned context before asynchronous
// work starts, so this module never calls a solver re-entrantly from a user
// propagator callback.
class ImpliedEqualityPartitionRefiner
{
    struct Impl;
    std::unique_ptr<Impl> m_impl;

public:
    ImpliedEqualityPartitionRefiner(
        z3::context &source_context,
        const std::vector<z3::expr> &constraints,
        const std::vector<z3::expr> &terms,
        const Options &options = {},
        util::Logger *log = nullptr);
    ~ImpliedEqualityPartitionRefiner();

    ImpliedEqualityPartitionRefiner(
        const ImpliedEqualityPartitionRefiner &) = delete;
    ImpliedEqualityPartitionRefiner &operator=(
        const ImpliedEqualityPartitionRefiner &) = delete;

    void start();
    bool ready() const;
    const Result &wait();
};

const char *status_name(Status status);

} // namespace util::eqpartition
