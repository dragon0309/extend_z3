#pragma once

#include <Singular/libsingular.h>
#include <gmpxx.h>

#include <string>
#include <vector>

namespace util
{
class Logger;
}

namespace util::gb
{

struct GbPreprocessStats
{
    int gens_before = 0;
    int gens_after = 0;
    int terms_before = 0;
    int terms_after = 0;
    mpz_class coeff_abs_before = 0;
    mpz_class coeff_abs_after = 0;
    mpz_class constant_gcd = 0;
    int constants_merged = 0;
    int content_gcd_replacements = 0;
    int coefficient_canonicalizations = 0;
};

// The caller owns every non-null poly stored in gens and targets. This function
// mutates both vectors in place and may delete or replace their elements. After
// it returns, the caller owns the resulting elements and must not use any old
// poly identities that may have been replaced.
//
// Singular's current ring is changed to R and is intentionally not restored.
void preprocess_groebner_inputs(std::vector<poly> &gens,
                                std::vector<poly> &targets,
                                const ring R,
                                const std::string &label,
                                GbPreprocessStats &stats,
                                util::Logger *logger = nullptr,
                                std::vector<int> *gen_origins = nullptr);

} // namespace util::gb
