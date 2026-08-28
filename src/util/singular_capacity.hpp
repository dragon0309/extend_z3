#pragma once

#include <Singular/libsingular.h>

#include <cstddef>
#include <limits>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>

namespace util::singular
{

// Derive the capacity from the actual ring::N field exposed by the Singular
// headers used for this build.  This deliberately avoids assuming that every
// Singular ABI stores the variable count in a short.
using RingVariableCount = std::remove_cv_t<std::remove_reference_t<
    decltype(std::declval<ring>()->N)>>;

constexpr std::size_t ring_variable_limit() noexcept
{
    return static_cast<std::size_t>(
        std::numeric_limits<RingVariableCount>::max());
}

inline void require_ring_variable_capacity(
    std::size_t requested,
    std::size_t limit = ring_variable_limit())
{
    if (requested > limit)
        throw std::runtime_error(
            "Singular ring variable capacity exceeded before ring construction: requested=" +
            std::to_string(requested) + " limit=" + std::to_string(limit));
}

} // namespace util::singular
