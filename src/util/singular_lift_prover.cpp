#include "util/singular_lift_prover.hpp"

#include <algorithm>
#include <unordered_set>
#include <utility>

#include "util/gb_preprocess.hpp"
#include "util/singular_dump.hpp"

namespace util::singular
{
namespace
{

void delete_poly(poly &p, ring R)
{
    if (p != nullptr)
        p_Delete(&p, R);
    p = nullptr;
}

void delete_polys(std::vector<poly> &polys, ring R)
{
    rChangeCurrRing(R);
    for (poly &p : polys)
        delete_poly(p, R);
    polys.clear();
}

poly copy_lift_vector_component(ideal lift,
                                std::size_t index,
                                std::size_t component_count,
                                ring R)
{
    rChangeCurrRing(R);
    if (lift == nullptr || index >= component_count)
        return nullptr;

    auto has_module_components = [R](poly value)
    {
        for (poly term = value; term != nullptr; term = pNext(term))
            if (p_GetComp(term, R) != 0)
                return true;
        return false;
    };

    poly direct = nullptr;
    if (lift->nrows == static_cast<int>(component_count) && lift->ncols >= 1)
        direct = MATELEM((matrix)lift, static_cast<int>(index) + 1, 1);
    else if (lift->nrows <= 1 && IDELEMS(lift) == static_cast<int>(component_count))
        direct = lift->m[static_cast<int>(index)];
    else if (index < static_cast<std::size_t>(IDELEMS(lift)))
        direct = lift->m[static_cast<int>(index)];

    if (direct != nullptr && !has_module_components(direct))
        return p_Copy(direct, R);

    poly output = nullptr;
    const long wanted_component = static_cast<long>(index) + 1;
    for (int i = 0; i < IDELEMS(lift); ++i)
    {
        for (poly term = lift->m[i]; term != nullptr; term = pNext(term))
        {
            if (p_GetComp(term, R) != wanted_component)
                continue;
            poly single = p_Head(term, R);
            p_SetComp(single, 0, R);
            p_Setm(single, R);
            output = p_Add_q(output, single, R);
        }
    }
    return output;
}

std::vector<std::size_t> extract_support(ideal source,
                                         poly target,
                                         const std::vector<int> &origins,
                                         ring R,
                                         const std::string &label,
                                         bool &certified,
                                         util::Logger *log)
{
    certified = false;
    std::vector<std::size_t> support;
    if (target == nullptr)
    {
        certified = true;
        return support;
    }
    if (source == nullptr || origins.empty())
        return support;

    ideal submodule = idInit(1, 1);
    submodule->m[0] = p_Copy(target, R);
    ideal remainder = nullptr;
    ideal certificate = util::singular::lift(
        source, submodule, &remainder, R, label);
    rChangeCurrRing(R);
    certified = certificate != nullptr &&
                (remainder == nullptr || idIs0(remainder));
    if (certified)
    {
        std::unordered_set<std::size_t> original_indices;
        for (std::size_t i = 0; i < origins.size(); ++i)
        {
            poly coefficient = copy_lift_vector_component(
                certificate, i, origins.size(), R);
            if (coefficient != nullptr)
            {
                if (origins[i] >= 0)
                    original_indices.insert(static_cast<std::size_t>(origins[i]));
                delete_poly(coefficient, R);
            }
        }
        support.assign(original_indices.begin(), original_indices.end());
        std::sort(support.begin(), support.end());
    }
    else if (log)
    {
        LOG_INFO(*log, "singular", label + ": direct lift certificate failed");
    }

    if (certificate)
        idDelete(&certificate);
    if (remainder)
        idDelete(&remainder);
    if (submodule)
        idDelete(&submodule);
    return support;
}

} // namespace

LiftBatchResult prove_with_lift_support(
    const std::vector<poly> &generators,
    const std::vector<poly> &targets,
    const std::vector<std::string> &target_labels,
    ring R,
    const LiftProverOptions &options,
    const std::string &label,
    util::Logger *log)
{
    LiftBatchResult result;
    result.input_generator_count = generators.size();
    result.targets.resize(targets.size());
    if (R == nullptr)
        return result;
    rChangeCurrRing(R);

    std::vector<poly> owned_generators;
    std::vector<poly> owned_targets;
    std::vector<poly> raw_generators;
    std::vector<int> origins;
    ideal source = nullptr;
    ideal basis = nullptr;
    try
    {
        owned_generators.reserve(generators.size());
        origins.reserve(generators.size());
        for (std::size_t i = 0; i < generators.size(); ++i)
        {
            owned_generators.push_back(generators[i] ? p_Copy(generators[i], R) : nullptr);
            origins.push_back(static_cast<int>(i));
        }
        owned_targets.reserve(targets.size());
        for (poly target : targets)
            owned_targets.push_back(target ? p_Copy(target, R) : nullptr);

        if (options.preprocess)
        {
            if (options.verify_preprocess)
            {
                raw_generators.reserve(owned_generators.size());
                for (poly generator : owned_generators)
                    raw_generators.push_back(generator ? p_Copy(generator, R) : nullptr);
            }
            util::gb::GbPreprocessStats stats;
            util::gb::preprocess_groebner_inputs(
                owned_generators, owned_targets, R, label, stats, log, &origins);
            if (options.verify_preprocess)
                membership_detail::verify_ideal_equality(
                    raw_generators, owned_generators, R, label,
                    result.groebner, log);
        }

        result.preprocessed_generator_count = owned_generators.size();
        {
            std::unordered_set<std::size_t> active;
            for (int origin : origins)
                if (origin >= 0)
                    active.insert(static_cast<std::size_t>(origin));
            result.active_generator_indices.assign(active.begin(), active.end());
            std::sort(result.active_generator_indices.begin(),
                      result.active_generator_indices.end());
        }

        if (owned_generators.empty())
        {
            for (std::size_t i = 0; i < owned_targets.size(); ++i)
            {
                result.targets[i].member = owned_targets[i] == nullptr;
                result.targets[i].support_certified = result.targets[i].member;
            }
        }
        else
        {
            source = membership_detail::ideal_from_owned_polys(
                owned_generators, R);
            basis = membership_detail::timed_groebner(
                source, R, label, result.groebner, log);
            for (std::size_t i = 0; i < owned_targets.size(); ++i)
            {
                TargetLiftResult &target_result = result.targets[i];
                if (owned_targets[i] == nullptr)
                {
                    target_result.member = true;
                    target_result.support_certified = true;
                    continue;
                }
                poly normal = util::singular::normal_form(
                    basis, p_Copy(owned_targets[i], R), R, label);
                target_result.member = normal == nullptr;
                delete_poly(normal, R);
                if (target_result.member && options.extract_support)
                {
                    const std::string &target_label =
                        i < target_labels.size() ? target_labels[i] : label;
                    target_result.used_generator_indices = extract_support(
                        source, owned_targets[i], origins, R,
                        target_label, target_result.support_certified, log);
                }
            }
        }

        if (basis)
            idDelete(&basis);
        if (source)
            idDelete(&source);
        delete_polys(owned_generators, R);
        delete_polys(owned_targets, R);
        delete_polys(raw_generators, R);
        return result;
    }
    catch (...)
    {
        rChangeCurrRing(R);
        if (basis)
            idDelete(&basis);
        if (source)
            idDelete(&source);
        delete_polys(owned_generators, R);
        delete_polys(owned_targets, R);
        delete_polys(raw_generators, R);
        throw;
    }
}

} // namespace util::singular
