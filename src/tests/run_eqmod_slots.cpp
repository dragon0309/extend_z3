#include "util/eqmod_slots.hpp"
#include "eqmod_engine.hpp"

#include <iostream>
#include <stdexcept>
#include <type_traits>

static_assert(!std::is_copy_constructible_v<eqmod::P1Compiled>);
static_assert(!std::is_copy_assignable_v<eqmod::P1Compiled>);
static_assert(std::is_nothrow_move_constructible_v<eqmod::P1Compiled>);
static_assert(!std::is_copy_constructible_v<eqmod::NCompiled>);
static_assert(!std::is_copy_assignable_v<eqmod::NCompiled>);
static_assert(std::is_nothrow_move_constructible_v<eqmod::NCompiled>);

int main()
{
    z3::context source;
    z3::context target;
    const z3::expr p1 = source.bool_const("p1_atom");
    const z3::expr p3a = source.bool_const("p3_atom_a");
    const z3::expr p3b = source.bool_const("p3_atom_b");

    std::vector<z3::expr> source_p1{p1};
    std::vector<std::vector<z3::expr>> source_n(5);
    source_n[3] = {p3a, p3b};

    std::vector<z3::expr> translated_p1;
    util::eqmod::AstSlotMap p1_slots;
    std::vector<std::vector<z3::expr>> translated_n;
    std::vector<util::eqmod::AstSlotMap> n_slots;
    util::eqmod::translate_atom_slots(
        target, source_p1, source_n, translated_p1, p1_slots,
        translated_n, n_slots);

    if (translated_p1.size() != 1 || translated_n[3].size() != 2 ||
        p1_slots.at((Z3_ast)translated_p1[0]) != 0 ||
        n_slots[3].at((Z3_ast)translated_n[3][0]) != 0 ||
        n_slots[3].at((Z3_ast)translated_n[3][1]) != 1)
        throw std::runtime_error("translated eqmod slots are not stable");

    std::vector<std::string> p1_qvars{"u_mod_0_0"};
    std::vector<std::vector<std::vector<std::string>>> qvars(5);
    qvars[2] = {};
    qvars[3] = {{"u_mod_2_0_0", "u_mod_2_0_1", "u_mod_2_0_2"},
                {"u_mod_2_1_0", "u_mod_2_1_1", "u_mod_2_1_2"}};
    qvars[4] = {};
    util::eqmod::require_preallocated_qvar_slots(
        source_p1.size(), p1_qvars, source_n, qvars);

    bool missing_qvar_rejected = false;
    qvars[3][1].pop_back();
    try
    {
        util::eqmod::require_preallocated_qvar_slots(
            source_p1.size(), p1_qvars, source_n, qvars);
    }
    catch (const std::runtime_error &)
    {
        missing_qvar_rejected = true;
    }
    if (!missing_qvar_rejected)
        throw std::runtime_error("missing qvar slot was not a hard failure");

    bool duplicate_rejected = false;
    try
    {
        std::vector<z3::expr> duplicate_p1{p1, p1};
        util::eqmod::translate_atom_slots(
            target, duplicate_p1, source_n, translated_p1, p1_slots,
            translated_n, n_slots);
    }
    catch (const std::runtime_error &)
    {
        duplicate_rejected = true;
    }
    if (!duplicate_rejected)
        throw std::runtime_error("duplicate translated AST was not rejected");

    std::cout << "eqmod fresh/stable-slot tests passed\n";
    return 0;
}
