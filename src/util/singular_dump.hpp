#pragma once

#include <Singular/libsingular.h>

#include <string>

#include "util/logger.hpp"

namespace util::singular
{

/** Runtime configuration for replayable Singular API dumps. */
struct DumpConfig
{
    bool enabled = false;
    std::string output_dir = "logs/singular";
    util::Logger *logger = nullptr;
};

/**
 * Configure the process-wide recorder. Calling this resets all basis-to-dump
 * associations. Existing dump files are preserved and numbering continues
 * after the greatest existing call number.
 */
void configure_dump(DumpConfig config);

bool dump_enabled();

/** Execute kStd and, when enabled, create one replayable .sing file. */
ideal groebner(ideal input, ring R, const std::string &label = {});

/**
 * Execute kNF. If basis came from groebner(), append this NF calculation to the
 * same file; otherwise create a standalone NF replay file.
 *
 * target has exactly the same ownership semantics as the poly argument passed
 * directly to kNF.
 */
poly normal_form(ideal basis, poly target, ring R, const std::string &label = {});

/** Execute the idLift form used by main and create one replayable lift file. */
ideal lift(ideal source,
           ideal submodule,
           ideal *remainder,
           ring R,
           const std::string &label = {});

} // namespace util::singular
