#include "util/singular_capacity.hpp"

#include <iostream>
#include <stdexcept>

int main()
{
    const std::size_t abi_limit = util::singular::ring_variable_limit();
    if (abi_limit == 0)
        throw std::runtime_error("Singular ABI reported a zero variable limit");
    util::singular::require_ring_variable_capacity(abi_limit, abi_limit);

    bool rejected = false;
    try
    {
        util::singular::require_ring_variable_capacity(9, 8);
    }
    catch (const std::runtime_error &)
    {
        rejected = true;
    }
    if (!rejected)
        throw std::runtime_error("over-limit preflight was not rejected");
    std::cout << "Singular ring capacity preflight tests passed (ABI limit="
              << abi_limit << ")\n";
    return 0;
}
