#include "util/singular_membership_prover.hpp"

#include <algorithm>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "util/fmt_duration.hpp"
#include "util/gb_preprocess.hpp"
#include "util/singular_dump.hpp"

namespace util::singular
{
namespace
{

using clk = std::chrono::steady_clock;

void delete_poly(poly &value, ring R)
{
    if (value != nullptr)
        p_Delete(&value, R);
    value = nullptr;
}

void delete_polys(std::vector<poly> &values, ring R)
{
    rChangeCurrRing(R);
    for (poly &value : values)
        delete_poly(value, R);
    values.clear();
}

std::string poly_to_string(poly value, ring R)
{
    if (value == nullptr)
        return "0";
    char *raw = p_String(value, R);
    std::string result = raw ? std::string(raw) : std::string("?");
    if (raw)
        omFree(raw);
    return result;
}

std::vector<bool> raw_membership(std::vector<poly> owned_generators,
                                 const std::vector<poly> &targets,
                                 ring R,
                                 const std::string &label,
                                 std::vector<std::string> *normal_forms,
                                 GroebnerTiming &timing,
                                 util::Logger *log)
{
    rChangeCurrRing(R);
    std::vector<bool> membership(targets.size(), false);
    if (normal_forms)
        normal_forms->assign(targets.size(), "not-computed");
    if (owned_generators.empty())
    {
        for (std::size_t i = 0; i < targets.size(); ++i)
        {
            membership[i] = targets[i] == nullptr;
            if (normal_forms)
                (*normal_forms)[i] = poly_to_string(targets[i], R);
        }
        return membership;
    }

    ideal source = membership_detail::ideal_from_owned_polys(owned_generators, R);
    ideal basis = membership_detail::timed_groebner(
        source, R, label, timing, log);
    for (std::size_t i = 0; i < targets.size(); ++i)
    {
        if (targets[i] == nullptr)
        {
            membership[i] = true;
            if (normal_forms)
                (*normal_forms)[i] = "0";
            continue;
        }
        poly normal = util::singular::normal_form(
            basis, p_Copy(targets[i], R), R, label);
        membership[i] = normal == nullptr;
        if (normal_forms)
            (*normal_forms)[i] = poly_to_string(normal, R);
        delete_poly(normal, R);
    }
    if (basis)
        idDelete(&basis);
    if (source)
        idDelete(&source);
    return membership;
}

} // namespace

namespace membership_detail
{

ideal ideal_from_owned_polys(std::vector<poly> &polys, ring R)
{
    rChangeCurrRing(R);
    ideal result = idInit(static_cast<int>(polys.size()), 1);
    for (std::size_t i = 0; i < polys.size(); ++i)
    {
        result->m[static_cast<int>(i)] = polys[i];
        polys[i] = nullptr;
    }
    return result;
}

ideal timed_groebner(ideal input,
                     ring R,
                     const std::string &label,
                     GroebnerTiming &timing,
                     util::Logger *log)
{
    rChangeCurrRing(R);
    const auto started = clk::now();
    ideal basis = util::singular::groebner(input, R, label);
    const auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
        clk::now() - started);
    ++timing.calls;
    timing.elapsed += elapsed;
    if (log)
    {
        std::ostringstream message;
        message << "Groebner basis std";
        if (!label.empty())
            message << " [" << label << "]";
        message << " finished in " << util::fmt_duration(elapsed);
        LOG_INFO(*log, "singular", message.str());
    }
    return basis;
}

void verify_ideal_equality(const std::vector<poly> &raw_generators,
                           const std::vector<poly> &optimized_generators,
                           ring R,
                           const std::string &label,
                           GroebnerTiming &timing,
                           util::Logger *log)
{
    std::vector<poly> optimized_owned;
    optimized_owned.reserve(optimized_generators.size());
    for (poly generator : optimized_generators)
        optimized_owned.push_back(generator ? p_Copy(generator, R) : nullptr);
    std::vector<std::string> raw_normal_forms;
    const std::vector<bool> raw_in_optimized = raw_membership(
        std::move(optimized_owned), raw_generators, R,
        label + "-verify-ideal-optimized", &raw_normal_forms, timing, log);

    std::vector<poly> raw_owned;
    raw_owned.reserve(raw_generators.size());
    for (poly generator : raw_generators)
        raw_owned.push_back(generator ? p_Copy(generator, R) : nullptr);
    std::vector<std::string> optimized_normal_forms;
    const std::vector<bool> optimized_in_raw = raw_membership(
        std::move(raw_owned), optimized_generators, R,
        label + "-verify-ideal-raw", &optimized_normal_forms, timing, log);

    const bool raw_contained = std::all_of(
        raw_in_optimized.begin(), raw_in_optimized.end(), [](bool value) { return value; });
    const bool optimized_contained = std::all_of(
        optimized_in_raw.begin(), optimized_in_raw.end(), [](bool value) { return value; });
    if (!raw_contained || !optimized_contained)
    {
        std::ostringstream message;
        message << "GB preprocess ideal verification failed [" << label << "]";
        for (std::size_t i = 0; i < raw_in_optimized.size(); ++i)
            if (!raw_in_optimized[i])
                message << "\n  raw generator #" << i
                        << " is not in optimized ideal ; gen="
                        << poly_to_string(raw_generators[i], R)
                        << " ; nf=" << raw_normal_forms[i];
        for (std::size_t i = 0; i < optimized_in_raw.size(); ++i)
            if (!optimized_in_raw[i])
                message << "\n  optimized generator #" << i
                        << " is not in raw ideal ; gen="
                        << poly_to_string(optimized_generators[i], R)
                        << " ; nf=" << optimized_normal_forms[i];
        if (log)
            LOG_INFO(*log, "singular", message.str());
        throw std::runtime_error(message.str());
    }
    if (log)
        LOG_INFO(*log, "singular",
                 "[gb-preprocess] " + label +
                     ": verify ideal equality OK; raw_gens=" +
                     std::to_string(raw_generators.size()) +
                     " optimized_gens=" + std::to_string(optimized_generators.size()));
}

} // namespace membership_detail

MembershipBatchResult prove_membership(
    const std::vector<poly> &generators,
    const std::vector<poly> &targets,
    ring R,
    const MembershipOptions &options,
    const std::string &label,
    util::Logger *log)
{
    MembershipBatchResult result;
    result.membership.assign(targets.size(), false);
    result.normal_forms.assign(targets.size(), "not-computed");
    if (R == nullptr)
        return result;
    rChangeCurrRing(R);

    std::vector<poly> owned_generators;
    std::vector<poly> owned_targets;
    std::vector<poly> raw_generators;
    std::vector<poly> raw_targets;
    try
    {
        owned_generators.reserve(generators.size());
        for (poly generator : generators)
            owned_generators.push_back(generator ? p_Copy(generator, R) : nullptr);
        owned_targets.reserve(targets.size());
        for (poly target : targets)
            owned_targets.push_back(target ? p_Copy(target, R) : nullptr);

        if (options.verify_preprocess)
        {
            raw_generators.reserve(owned_generators.size());
            for (poly generator : owned_generators)
                raw_generators.push_back(generator ? p_Copy(generator, R) : nullptr);
            raw_targets.reserve(targets.size());
            for (poly target : targets)
                raw_targets.push_back(target ? p_Copy(target, R) : nullptr);
        }

        if (options.preprocess)
        {
            result.used_preprocess = true;
            util::gb::GbPreprocessStats stats;
            util::gb::preprocess_groebner_inputs(
                owned_generators, owned_targets, R, label, stats, log);
        }

        if (options.verify_preprocess)
            membership_detail::verify_ideal_equality(
                raw_generators, owned_generators, R, label, result.groebner, log);

        result.membership = raw_membership(
            std::move(owned_generators), owned_targets, R, label,
            &result.normal_forms, result.groebner, log);

        if (options.verify_preprocess)
        {
            std::vector<std::string> raw_normal_forms;
            const std::vector<bool> raw_membership_result = raw_membership(
                std::move(raw_generators), raw_targets, R,
                label + "-verify-raw", &raw_normal_forms, result.groebner, log);
            if (raw_membership_result != result.membership)
            {
                std::ostringstream message;
                message << "GB preprocess verification failed [" << label << "]";
                for (std::size_t i = 0; i < raw_membership_result.size(); ++i)
                    message << "\n  target#" << i
                            << " raw=" << (raw_membership_result[i] ? "true" : "false")
                            << " optimized=" << (result.membership[i] ? "true" : "false")
                            << " raw_nf=" << raw_normal_forms[i]
                            << " opt_nf=" << result.normal_forms[i];
                if (log)
                    LOG_INFO(*log, "singular", message.str());
                throw std::runtime_error(message.str());
            }
            if (log)
                LOG_INFO(*log, "singular",
                         "[gb-preprocess] " + label + ": verify membership OK");
        }

        delete_polys(owned_generators, R);
        delete_polys(owned_targets, R);
        delete_polys(raw_generators, R);
        delete_polys(raw_targets, R);
        return result;
    }
    catch (...)
    {
        rChangeCurrRing(R);
        delete_polys(owned_generators, R);
        delete_polys(owned_targets, R);
        delete_polys(raw_generators, R);
        delete_polys(raw_targets, R);
        throw;
    }
}

} // namespace util::singular
