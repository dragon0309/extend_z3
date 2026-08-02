#pragma once

#include <z3++.h>

#include <vector>

#include "util/implied_eq_partition_refiner.hpp"

namespace util
{
class Logger;
}

namespace util::eqpartition
{

enum class Variant
{
    Z3Mpm,
    Hipr,
    Ipr,
    Abipr,
    Sopr,
    Hsopr,
    ParallelBpr
};

const char *variant_name(Variant variant);

struct VariantOptions
{
    std::size_t parallel_workers = 4;
    bool parallel_final_global_validation = false;
};

// Experimental alternatives used only when explicitly selected by the
// partition-prepass CLI. The existing ImpliedEqualityPartitionRefiner remains
// the default implementation and does not call this function.
Result run_variant(
    z3::context &source_context,
    const std::vector<z3::expr> &source_constraints,
    const std::vector<z3::expr> &source_terms,
    Variant variant,
    util::Logger *log = nullptr);

Result run_variant(
    z3::context &source_context,
    const std::vector<z3::expr> &source_constraints,
    const std::vector<z3::expr> &source_terms,
    Variant variant,
    const VariantOptions &options,
    util::Logger *log = nullptr);

} // namespace util::eqpartition
