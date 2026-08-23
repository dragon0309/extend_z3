#include "smt2_frontend.hpp"

#include <z3.h>

#include <fstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace smt2
{
namespace
{

constexpr const char *poly_prelude = R"PRE(
(declare-datatype Poly
  (par (T)
    ((PConst (const_c T))
     (PVar   (var_name String))
     (PNeg   (neg_p (Poly T)))
     (PAdd   (add_l (Poly T)) (add_r (Poly T)))
     (PSub   (sub_l (Poly T)) (sub_r (Poly T)))
     (PMul   (mul_l (Poly T)) (mul_r (Poly T)))
     (PPow   (pow_base (Poly T)) (pow_k Int)))))

(declare-fun eqP ((Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP1 ((Poly Int) (Poly Int) (Poly Int)) Bool)

; kept for future
(declare-fun eqmodP2 ((Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP3 ((Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP4 ((Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
)PRE";

bool contains_poly_declaration(const std::string &script)
{
    if (script.find("(declare-datatype Poly") != std::string::npos)
        return true;
    return script.find("(declare-datatypes") != std::string::npos &&
           script.find("Poly") != std::string::npos;
}

std::string inject_after_set_logic(
    const std::string &raw,
    const std::string &insertion)
{
    const std::size_t position = raw.find("(set-logic");
    if (position == std::string::npos)
        return insertion + "\n" + raw;

    const std::size_t line_end = raw.find('\n', position);
    if (line_end == std::string::npos)
        return raw + "\n" + insertion;

    std::string result;
    result.reserve(raw.size() + insertion.size() + 8);
    result.append(raw, 0, line_end + 1);
    result.append(insertion);
    result.push_back('\n');
    result.append(raw, line_end + 1, std::string::npos);
    return result;
}

} // namespace

std::string read_file(const std::string &filename)
{
    std::ifstream input(filename, std::ios::in | std::ios::binary);
    if (!input)
        throw std::runtime_error("cannot open file: " + filename);

    std::string contents;
    input.seekg(0, std::ios::end);
    contents.resize(static_cast<std::size_t>(input.tellg()));
    input.seekg(0, std::ios::beg);
    if (!contents.empty())
        input.read(contents.data(), static_cast<std::streamsize>(contents.size()));
    return contents;
}

std::string inject_poly_prelude_if_missing(const std::string &raw)
{
    if (contains_poly_declaration(raw))
        return raw;
    return inject_after_set_logic(raw, poly_prelude);
}

std::vector<z3::expr> parse_assertions(
    z3::context &context,
    const std::string &script)
{
    const Z3_context raw_context = static_cast<Z3_context>(context);
    const Z3_ast_vector parsed = Z3_parse_smtlib2_string(
        raw_context, script.c_str(),
        0, nullptr, nullptr,
        0, nullptr, nullptr);

    const Z3_error_code error = Z3_get_error_code(raw_context);
    if (error != Z3_OK)
        throw z3::exception(Z3_get_error_msg(raw_context, error));

    const unsigned size = Z3_ast_vector_size(raw_context, parsed);
    std::vector<z3::expr> assertions;
    assertions.reserve(size);
    for (unsigned index = 0; index < size; ++index)
        assertions.emplace_back(
            context, Z3_ast_vector_get(raw_context, parsed, index));
    return assertions;
}

std::vector<z3::expr> load_assertions(
    z3::context &context,
    const std::string &filename)
{
    return parse_assertions(
        context, inject_poly_prelude_if_missing(read_file(filename)));
}

} // namespace smt2
