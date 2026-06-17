#pragma once

#include <Singular/libsingular.h>
#include <gmpxx.h>

#include <string>
#include <vector>

namespace util
{
class Logger;
}

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
    int content_divisions = 0;
    int coefficient_canonicalizations = 0;
    int unit_normalizations = 0;
    int monic_reducers = 0;
    int monic_reductions = 0;
    int duplicate_drops = 0;
};

void preprocess_groebner_inputs(std::vector<poly> &gens,
                                std::vector<poly> &targets,
                                const ring R,
                                const std::string &label,
                                GbPreprocessStats &stats,
                                util::Logger *logger = nullptr);
