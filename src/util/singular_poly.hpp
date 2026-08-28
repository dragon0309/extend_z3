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

// Small transaction guard for lowering code.  Singular polynomials are raw
// pointers whose deletion also needs the owning ring, so std::unique_ptr is
// not a natural fit.  This guard keeps partially lowered expressions from
// leaking when a later child is unsupported or another C++ exception is
// raised.
class ScopedPolyOwner
{
    poly value_ = nullptr;
    ring ring_ = nullptr;

public:
    explicit ScopedPolyOwner(ring R, poly value = nullptr) noexcept
        : value_(value), ring_(R) {}
    ~ScopedPolyOwner();

    ScopedPolyOwner(const ScopedPolyOwner &) = delete;
    ScopedPolyOwner &operator=(const ScopedPolyOwner &) = delete;

    ScopedPolyOwner(ScopedPolyOwner &&other) noexcept;
    ScopedPolyOwner &operator=(ScopedPolyOwner &&other) noexcept;

    poly get() const noexcept { return value_; }
    poly release() noexcept;
    void reset(poly value = nullptr) noexcept;
};

class ScopedPolyVectorOwner
{
    std::vector<poly> values_;
    ring ring_ = nullptr;

public:
    explicit ScopedPolyVectorOwner(ring R) noexcept : ring_(R) {}
    ~ScopedPolyVectorOwner();

    ScopedPolyVectorOwner(const ScopedPolyVectorOwner &) = delete;
    ScopedPolyVectorOwner &operator=(const ScopedPolyVectorOwner &) = delete;

    std::vector<poly> &values() noexcept { return values_; }
    std::vector<poly> release() noexcept;
};

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
