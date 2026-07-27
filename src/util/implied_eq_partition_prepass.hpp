#pragma once

#include <z3++.h>

#include <cstddef>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "util/implied_eq_partition_refiner.hpp"
#include "util/implied_eq_partition_variants.hpp"

namespace util
{
class Logger;
}

namespace util::eqpartition
{

struct PrepassResult
{
    std::size_t constraints = 0;
    std::size_t terms = 0;
    std::size_t injected_eqps = 0;
    // True when the initial plain non-Poly constraint check returned UNSAT.
    // In this case prepass intentionally injects nothing and lets the normal
    // main pipeline solve the original assertions.
    bool constraints_unsat = false;
    Statistics partition_statistics;
    std::vector<std::pair<std::string, std::string>> equalities;
    // Native BV pairs corresponding one-for-one with equalities/assertions.
    // They are retained so the main user propagator can optionally replay the
    // complete prepass result after Z3 search has entered a legal callback.
    std::vector<std::pair<z3::expr, z3::expr>> native_equalities;
    std::vector<z3::expr> assertions;
};

struct PrepassOptions
{
    // Empty preserves the existing fresh-solver BPR implementation exactly.
    std::optional<Variant> experimental_variant;
    std::size_t parallel_workers = 4;
    bool parallel_final_global_validation = false;
};

// Runs complete implied-equality partition refinement before the main Z3
// solver is constructed. If the non-Poly constraints are satisfiable, encodes
// every pair in every complete equality class as an eqP assertion. If they are
// UNSAT, returns no assertions so the normal main pipeline solves the original
// formula. Every returned equality is global with respect to the selected
// non-Poly BV constraint subset.
PrepassResult run_eqp_prepass(
    z3::context &context,
    const std::vector<z3::expr> &source_assertions,
    util::Logger *log = nullptr);

PrepassResult run_eqp_prepass(
    z3::context &context,
    const std::vector<z3::expr> &source_assertions,
    const PrepassOptions &options,
    util::Logger *log = nullptr);

} // namespace util::eqpartition
