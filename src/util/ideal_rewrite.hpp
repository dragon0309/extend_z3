#pragma once

#include <Singular/libsingular.h>

#include <chrono>
#include <cstddef>
#include <string>
#include <vector>

#include "util/logger.hpp"

namespace util::ideal_rewrite
{

struct IdealRewriteStats
{
    std::size_t input_generators = 0;
    std::size_t output_generators = 0;
    std::size_t input_targets = 0;
    std::size_t rounds = 0;
    std::size_t rules_extracted = 0;
    std::size_t generators_rewritten = 0;
    std::size_t targets_rewritten = 0;
    std::size_t zero_generators_dropped = 0;
    std::size_t duplicate_generators_dropped = 0;
    std::size_t cycle_worklist_steps = 0;
    std::chrono::nanoseconds elapsed{0};
};

// Rewrites owned Singular polynomials in place. A rule is extracted only from
// a monic linear generator x-rhs, so eliminating it and substituting x -> rhs
// in both the remaining generators and the targets preserves ideal-membership
// answers. The extraction/DAG composition/worklist structure mirrors the
// assertion rewrite pipeline, but this module has no dependency on rewrite.cpp.
void rewrite_inputs(std::vector<poly> &owned_generators,
                    std::vector<poly> &owned_targets,
                    ring R,
                    const std::string &label,
                    IdealRewriteStats &stats,
                    util::Logger *log = nullptr);

} // namespace util::ideal_rewrite
