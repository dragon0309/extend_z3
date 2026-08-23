#pragma once

#include <z3++.h>

#include <string>
#include <vector>

namespace smt2
{

std::string read_file(const std::string &filename);

std::string inject_poly_prelude_if_missing(const std::string &raw);

std::vector<z3::expr> parse_assertions(
    z3::context &context,
    const std::string &script);

std::vector<z3::expr> load_assertions(
    z3::context &context,
    const std::string &filename);

} // namespace smt2
