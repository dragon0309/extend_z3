#pragma once

#include <Singular/libsingular.h>

#include <cstddef>
#include <memory>
#include <string>
#include <vector>

#include "util/singular_membership_prover.hpp"

namespace util
{
class Logger;
}

namespace util::singular
{

// Every group represents one ideal <base_generators, extra_generators> and a
// batch of targets queried against that ideal. Polynomial pointers are
// borrowed for the duration of run().
struct MembershipGroup
{
    std::vector<poly> extra_generators;
    std::vector<poly> targets;
    std::string label;
};

struct MembershipGroupBatchOptions
{
    MembershipOptions membership;
    bool reuse_base_basis = false;
    bool return_normal_forms = false;
    std::size_t processes = 0;
};

struct MembershipGroupBatchResult
{
    std::vector<MembershipBatchResult> groups;
    GroebnerTiming base_groebner;
};

// Serial reference implementation. Besides being the default path, this is
// used to A/B base-basis reuse independently from process parallelism.
MembershipGroupBatchResult prove_membership_groups_serial(
    const std::vector<poly> &base_generators,
    const std::vector<MembershipGroup> &groups,
    ring R,
    const MembershipGroupBatchOptions &options,
    util::Logger *log = nullptr);

// Persistent worker processes are forked by the constructor. Construct this
// object before any application worker threads are started. Workers inherit a
// private copy of R and receive all later polynomial inputs through an exact
// sparse binary encoding, so no Singular pointer or mutable currRing state
// crosses a process boundary. Calls to run() on one pool are serialized. The
// ring uses integer (n_Z) coefficients, is borrowed, and must outlive the pool.
class MembershipProcessPool
{
    struct Impl;
    std::unique_ptr<Impl> m_impl;

public:
    MembershipProcessPool(ring R, std::size_t workers, util::Logger *log = nullptr);
    ~MembershipProcessPool();

    MembershipProcessPool(const MembershipProcessPool &) = delete;
    MembershipProcessPool &operator=(const MembershipProcessPool &) = delete;

    std::size_t workers() const;

    MembershipGroupBatchResult run(
        const std::vector<poly> &base_generators,
        const std::vector<MembershipGroup> &groups,
        const MembershipGroupBatchOptions &options);
};

} // namespace util::singular
