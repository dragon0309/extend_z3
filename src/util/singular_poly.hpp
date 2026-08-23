#pragma once

#include <Singular/libsingular.h>
#include <gmpxx.h>

#include <string>
#include <vector>

namespace util::singular
{

number num_from_si(long value, coeffs coefficients);
poly poly_from_mpz(const mpz_class &value, ring R);
poly poly_from_si(long value, ring R);
poly poly_one(ring R);

poly copy_poly_or_null(poly value, ring R);
void delete_poly_if_nonnull(poly &value, ring R);
void delete_polys(std::vector<poly> &values, ring R);

poly poly_mul_clone(poly lhs, poly rhs, ring R);
poly poly_mul_clone_or_zero(poly lhs, poly rhs, ring R);
poly poly_negate_owned(poly value, ring R);
poly poly_add_owned(poly lhs, poly rhs, ring R);
poly poly_sub_product_clone(poly base, poly multiplier, poly modulus, ring R);
poly build_eqmodP2_true_gen(poly difference,
                            poly first_multiplier,
                            poly first_modulus,
                            poly second_multiplier,
                            poly second_modulus,
                            ring R);

std::string poly_to_string(poly value, ring R);
std::string number_to_decimal_string(number value, ring R);
bool poly_equal(poly lhs, poly rhs, ring R);

} // namespace util::singular
