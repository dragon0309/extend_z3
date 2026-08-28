#include "util/singular_poly.hpp"

namespace util::singular
{

number num_from_si(long value, coeffs coefficients)
{
    mpz_t integer;
    mpz_init_set_si(integer, value);
    number result = n_InitMPZ(integer, coefficients);
    mpz_clear(integer);
    return result;
}

poly poly_from_mpz(const mpz_class &value, ring R)
{
    mpz_t integer;
    mpz_init_set(integer, value.get_mpz_t());
    number coefficient = n_InitMPZ(integer, R->cf);
    mpz_clear(integer);
    return p_NSet(coefficient, R);
}

poly poly_from_si(long value, ring R)
{
    return p_NSet(num_from_si(value, R->cf), R);
}

poly poly_one(ring R)
{
    return poly_from_si(1, R);
}

poly copy_poly_or_null(poly value, ring R)
{
    return value ? p_Copy(value, R) : nullptr;
}

void delete_poly_if_nonnull(poly &value, ring R)
{
    if (value)
        p_Delete(&value, R);
    value = nullptr;
}

void delete_polys(std::vector<poly> &values, ring R)
{
    if (R)
        rChangeCurrRing(R);
    for (poly &value : values)
        delete_poly_if_nonnull(value, R);
    values.clear();
}

ScopedPolyOwner::~ScopedPolyOwner()
{
    if (value_ && ring_)
    {
        rChangeCurrRing(ring_);
        delete_poly_if_nonnull(value_, ring_);
    }
}

ScopedPolyOwner::ScopedPolyOwner(ScopedPolyOwner &&other) noexcept
    : value_(other.release()), ring_(other.ring_)
{
}

ScopedPolyOwner &ScopedPolyOwner::operator=(ScopedPolyOwner &&other) noexcept
{
    if (this == &other)
        return *this;
    reset();
    ring_ = other.ring_;
    value_ = other.release();
    return *this;
}

poly ScopedPolyOwner::release() noexcept
{
    poly value = value_;
    value_ = nullptr;
    return value;
}

void ScopedPolyOwner::reset(poly value) noexcept
{
    if (value_ && ring_)
    {
        rChangeCurrRing(ring_);
        delete_poly_if_nonnull(value_, ring_);
    }
    value_ = value;
}

ScopedPolyVectorOwner::~ScopedPolyVectorOwner()
{
    delete_polys(values_, ring_);
}

std::vector<poly> ScopedPolyVectorOwner::release() noexcept
{
    std::vector<poly> values = std::move(values_);
    values_.clear();
    return values;
}

poly poly_mul_clone(poly lhs, poly rhs, ring R)
{
    return p_Mult_q(p_Copy(lhs, R), p_Copy(rhs, R), R);
}

poly poly_mul_clone_or_zero(poly lhs, poly rhs, ring R)
{
    if (!lhs || !rhs)
        return nullptr;
    return poly_mul_clone(lhs, rhs, R);
}

poly poly_negate_owned(poly value, ring R)
{
    if (!value)
        return nullptr;
    number minus_one = num_from_si(-1, R->cf);
    poly result = p_Mult_nn(value, minus_one, R);
    n_Delete(&minus_one, R->cf);
    return result;
}

poly poly_add_owned(poly lhs, poly rhs, ring R)
{
    if (!lhs)
        return rhs;
    if (!rhs)
        return lhs;
    return p_Add_q(lhs, rhs, R);
}

poly poly_sub_product_clone(poly base,
                            poly multiplier,
                            poly modulus,
                            ring R)
{
    return poly_add_owned(
        copy_poly_or_null(base, R),
        poly_negate_owned(
            poly_mul_clone_or_zero(multiplier, modulus, R), R),
        R);
}

poly build_eqmodP2_true_gen(poly difference,
                            poly first_multiplier,
                            poly first_modulus,
                            poly second_multiplier,
                            poly second_modulus,
                            ring R)
{
    poly intermediate = poly_sub_product_clone(
        difference, first_multiplier, first_modulus, R);
    poly result = poly_sub_product_clone(
        intermediate, second_multiplier, second_modulus, R);
    delete_poly_if_nonnull(intermediate, R);
    return result;
}

std::string poly_to_string(poly value, ring R)
{
    if (!value)
        return "0";
    char *raw = p_String(value, R);
    const std::string result = raw ? std::string(raw) : std::string("?");
    if (raw)
        omFree(raw);
    return result;
}

std::string number_to_decimal_string(number value, ring R)
{
    poly temporary = p_NSet(n_Copy(value, R->cf), R);
    const std::string result = poly_to_string(temporary, R);
    delete_poly_if_nonnull(temporary, R);
    return result;
}

bool poly_equal(poly lhs, poly rhs, ring R)
{
    rChangeCurrRing(R);
    if (!lhs && !rhs)
        return true;
    if (!lhs || !rhs)
        return false;
    poly difference = poly_add_owned(
        p_Copy(lhs, R), poly_negate_owned(p_Copy(rhs, R), R), R);
    const bool equal = difference == nullptr;
    delete_poly_if_nonnull(difference, R);
    return equal;
}

} // namespace util::singular
