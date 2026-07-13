#pragma once

#include <Singular/libsingular.h>

#include <chrono>
#include <cstddef>
#include <string>
#include <vector>

#include "util/logger.hpp"

namespace util::singular
{

struct GroebnerTiming
{
    std::size_t calls = 0;
    std::chrono::nanoseconds elapsed{0};
};

struct MembershipOptions
{
    bool preprocess = false;
    bool verify_preprocess = false;
};

struct MembershipBatchResult
{
    std::vector<bool> membership;
    std::vector<std::string> normal_forms;
    bool used_preprocess = false;
    GroebnerTiming groebner;
};

// generators and targets are borrowed. All Singular objects created by this
// workflow are copied and owned internally.
MembershipBatchResult prove_membership(
    const std::vector<poly> &generators,
    const std::vector<poly> &targets,
    ring R,
    const MembershipOptions &options,
    const std::string &label,
    util::Logger *log = nullptr);

// Shared implementation hooks for other Singular workflows such as lift.
// Inputs retain ownership unless explicitly described as owned.
namespace membership_detail
{

ideal ideal_from_owned_polys(std::vector<poly> &polys, ring R);

ideal timed_groebner(ideal input,
                     ring R,
                     const std::string &label,
                     GroebnerTiming &timing,
                     util::Logger *log = nullptr);

void verify_ideal_equality(const std::vector<poly> &raw_generators,
                           const std::vector<poly> &optimized_generators,
                           ring R,
                           const std::string &label,
                           GroebnerTiming &timing,
                           util::Logger *log = nullptr);

} // namespace membership_detail

} // namespace util::singular
