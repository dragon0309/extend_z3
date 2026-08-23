#pragma once

#include <optional>

#include "cli_options.hpp"
#include "util/implied_eq_partition_prepass.hpp"

namespace solver_options
{

// A missing value selects the prepass module's default overload, preserving
// its established production path when no experimental controls are present.
std::optional<util::eqpartition::PrepassOptions>
make_partition_prepass_options(const cli::Options &options);

} // namespace solver_options
