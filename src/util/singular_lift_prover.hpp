#pragma once

#include <Singular/libsingular.h>

#include <cstddef>
#include <string>
#include <vector>

#include "util/logger.hpp"
#include "util/singular_membership_prover.hpp"

namespace util::singular
{

struct LiftProverOptions
{
    bool preprocess = false;
    bool verify_preprocess = false;
    bool extract_support = false;
};

struct TargetLiftResult
{
    bool member = false;
    bool support_certified = false;
    std::vector<std::size_t> used_generator_indices;
};

struct LiftBatchResult
{
    std::vector<TargetLiftResult> targets;
    std::vector<std::size_t> active_generator_indices;
    std::size_t input_generator_count = 0;
    std::size_t preprocessed_generator_count = 0;
    GroebnerTiming groebner;
};

// generators and targets are borrowed. The module copies every non-null poly
// it needs and owns all copies, ideals, bases, and lift certificates it creates.
LiftBatchResult prove_with_lift_support(
    const std::vector<poly> &generators,
    const std::vector<poly> &targets,
    const std::vector<std::string> &target_labels,
    ring R,
    const LiftProverOptions &options,
    const std::string &label,
    util::Logger *log = nullptr);

} // namespace util::singular
