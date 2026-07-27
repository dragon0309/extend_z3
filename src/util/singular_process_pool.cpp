#include "util/singular_process_pool.hpp"

#include <algorithm>
#include <cerrno>
#include <climits>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <gmpxx.h>
#include <cstring>
#include <mutex>
#include <pthread.h>
#include <signal.h>
#include <stdexcept>
#include <string_view>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <utility>

#include "util/fmt_duration.hpp"
#include "util/gb_preprocess.hpp"
#include "util/logger.hpp"
#include "util/singular_dump.hpp"
#include "util/singular_runtime_stats.hpp"

namespace util::singular
{
namespace
{

using clk = std::chrono::steady_clock;
constexpr std::uint64_t kMaxFrameBytes = UINT64_C(1) << 34;
constexpr std::uint64_t kProtocolVersion = 4;
constexpr std::size_t kBaseBasisMinGroups = 8;

class ByteWriter
{
    std::vector<std::uint8_t> data_;

public:
    void put_u64(std::uint64_t value)
    {
        for (unsigned shift = 0; shift < 64; shift += 8)
            data_.push_back(static_cast<std::uint8_t>(value >> shift));
    }

    void put_bool(bool value) { data_.push_back(value ? 1 : 0); }

    void put_string(std::string_view value)
    {
        put_u64(value.size());
        data_.insert(data_.end(), value.begin(), value.end());
    }

    const std::vector<std::uint8_t> &data() const { return data_; }
};

class ByteReader
{
    const std::vector<std::uint8_t> &data_;
    std::size_t pos_ = 0;

    void require(std::size_t bytes)
    {
        if (bytes > data_.size() - std::min(pos_, data_.size()))
            throw std::runtime_error("truncated GB process-pool message");
    }

public:
    explicit ByteReader(const std::vector<std::uint8_t> &data) : data_(data) {}

    std::uint64_t get_u64()
    {
        require(8);
        std::uint64_t value = 0;
        for (unsigned shift = 0; shift < 64; shift += 8)
            value |= static_cast<std::uint64_t>(data_[pos_++]) << shift;
        return value;
    }

    bool get_bool()
    {
        require(1);
        const std::uint8_t value = data_[pos_++];
        if (value > 1)
            throw std::runtime_error("invalid boolean in GB process-pool message");
        return value != 0;
    }

    std::string get_string()
    {
        const std::uint64_t size64 = get_u64();
        if (size64 > data_.size() || size64 > SIZE_MAX)
            throw std::runtime_error("oversized string in GB process-pool message");
        const std::size_t size = static_cast<std::size_t>(size64);
        require(size);
        std::string value(reinterpret_cast<const char *>(data_.data() + pos_), size);
        pos_ += size;
        return value;
    }

    bool done() const { return pos_ == data_.size(); }
};

bool write_all(int fd, const void *raw, std::size_t bytes)
{
    sigset_t sigpipe_set;
    sigset_t previous_mask;
    sigemptyset(&sigpipe_set);
    sigaddset(&sigpipe_set, SIGPIPE);
    const int mask_error =
        pthread_sigmask(SIG_BLOCK, &sigpipe_set, &previous_mask);
    if (mask_error != 0)
    {
        errno = mask_error;
        return false;
    }
    const bool sigpipe_was_blocked =
        sigismember(&previous_mask, SIGPIPE) == 1;
    auto restore_sigpipe = [&]()
    {
        (void)pthread_sigmask(SIG_SETMASK, &previous_mask, nullptr);
    };

    const auto *data = static_cast<const std::uint8_t *>(raw);
    while (bytes != 0)
    {
        const ssize_t written = write(fd, data, bytes);
        if (written < 0)
        {
            if (errno == EINTR)
                continue;
            const int write_error = errno;
            if (write_error == EPIPE && !sigpipe_was_blocked)
            {
                struct timespec no_wait
                {
                };
                while (sigtimedwait(&sigpipe_set, nullptr, &no_wait) < 0 &&
                       errno == EINTR)
                {
                }
            }
            restore_sigpipe();
            errno = write_error;
            return false;
        }
        if (written == 0)
        {
            restore_sigpipe();
            errno = EIO;
            return false;
        }
        data += written;
        bytes -= static_cast<std::size_t>(written);
    }
    restore_sigpipe();
    return true;
}

bool read_all(int fd, void *raw, std::size_t bytes)
{
    auto *data = static_cast<std::uint8_t *>(raw);
    while (bytes != 0)
    {
        const ssize_t received = read(fd, data, bytes);
        if (received < 0)
        {
            if (errno == EINTR)
                continue;
            return false;
        }
        if (received == 0)
            return false;
        data += received;
        bytes -= static_cast<std::size_t>(received);
    }
    return true;
}

bool send_frame(int fd, const std::vector<std::uint8_t> &frame)
{
    const std::uint64_t size = frame.size();
    return write_all(fd, &size, sizeof(size)) &&
           (frame.empty() || write_all(fd, frame.data(), frame.size()));
}

bool receive_frame(int fd, std::vector<std::uint8_t> &frame)
{
    std::uint64_t size = 0;
    if (!read_all(fd, &size, sizeof(size)))
        return false;
    if (size > kMaxFrameBytes || size > SIZE_MAX)
        throw std::runtime_error("oversized GB process-pool frame");
    frame.resize(static_cast<std::size_t>(size));
    return frame.empty() || read_all(fd, frame.data(), frame.size());
}

std::string poly_to_wire(poly value, ring R)
{
    ByteWriter writer;
    std::size_t term_count = 0;
    for (poly term = value; term != nullptr; term = pNext(term))
        ++term_count;
    writer.put_u64(term_count);
    for (poly term = value; term != nullptr; term = pNext(term))
    {
        number coefficient = n_Copy(p_GetCoeff(term, R), R->cf);
        mpz_class integer;
        n_MPZ(integer.get_mpz_t(), coefficient, R->cf);
        writer.put_string(integer.get_str());
        n_Delete(&coefficient, R->cf);

        std::size_t nonzero_exponents = 0;
        for (int variable = 1; variable <= R->N; ++variable)
            if (p_GetExp(term, variable, R) != 0)
                ++nonzero_exponents;
        writer.put_u64(nonzero_exponents);
        for (int variable = 1; variable <= R->N; ++variable)
        {
            const int exponent = p_GetExp(term, variable, R);
            if (exponent == 0)
                continue;
            writer.put_u64(static_cast<std::uint64_t>(variable));
            writer.put_u64(static_cast<std::uint64_t>(exponent));
        }
    }
    return std::string(reinterpret_cast<const char *>(writer.data().data()),
                       writer.data().size());
}

poly poly_from_wire(const std::string &value, ring R)
{
    std::vector<std::uint8_t> bytes(value.begin(), value.end());
    ByteReader reader(bytes);
    const std::size_t term_count = reader.get_u64();
    poly result = nullptr;
    try
    {
        for (std::size_t term_index = 0; term_index < term_count; ++term_index)
        {
            const std::string coefficient_text = reader.get_string();
            mpz_class integer;
            if (integer.set_str(coefficient_text, 10) != 0)
                throw std::runtime_error(
                    "invalid coefficient in GB process-pool polynomial");
            number coefficient = n_InitMPZ(integer.get_mpz_t(), R->cf);
            poly term = p_NSet(coefficient, R);
            const std::size_t exponent_count = reader.get_u64();
            for (std::size_t i = 0; i < exponent_count; ++i)
            {
                const std::uint64_t variable = reader.get_u64();
                const std::uint64_t exponent = reader.get_u64();
                if (variable == 0 || variable > static_cast<std::uint64_t>(R->N) ||
                    exponent > static_cast<std::uint64_t>(INT_MAX))
                {
                    p_Delete(&term, R);
                    throw std::runtime_error(
                        "invalid exponent in GB process-pool polynomial");
                }
                p_SetExp(term, static_cast<int>(variable),
                         static_cast<int>(exponent), R);
            }
            p_Setm(term, R);
            result = result ? p_Add_q(result, term, R) : term;
        }
        if (!reader.done())
            throw std::runtime_error(
                "trailing bytes in GB process-pool polynomial");
        return result;
    }
    catch (...)
    {
        if (result)
            p_Delete(&result, R);
        throw;
    }
}

void delete_polys(std::vector<poly> &values, ring R)
{
    rChangeCurrRing(R);
    for (poly &value : values)
        if (value)
            p_Delete(&value, R);
    values.clear();
}

class PolyVectorGuard
{
    std::vector<poly> &values_;
    ring ring_;

public:
    PolyVectorGuard(std::vector<poly> &values, ring R)
        : values_(values), ring_(R)
    {
    }
    ~PolyVectorGuard() { delete_polys(values_, ring_); }
};

struct PreparedBase
{
    std::vector<poly> generators;
    GroebnerTiming groebner;
};

std::vector<poly> base_with_common_group_generators(
    const std::vector<poly> &base,
    const std::vector<MembershipGroup> &groups,
    ring R)
{
    std::vector<poly> result = base;
    if (groups.empty())
        return result;
    for (poly candidate : groups.front().extra_generators)
    {
        if (candidate == nullptr)
            continue;
        bool common = true;
        for (std::size_t group_index = 1; group_index < groups.size(); ++group_index)
        {
            bool found = false;
            for (poly other : groups[group_index].extra_generators)
                if (other != nullptr && p_EqualPolys(candidate, other, R))
                {
                    found = true;
                    break;
                }
            if (!found)
            {
                common = false;
                break;
            }
        }
        if (!common)
            continue;
        bool already_present = false;
        for (poly existing : result)
            if (existing != nullptr && p_EqualPolys(candidate, existing, R))
            {
                already_present = true;
                break;
            }
        if (!already_present)
            result.push_back(candidate);
    }
    return result;
}

PreparedBase prepare_base(const std::vector<poly> &base,
                          ring R,
                          const MembershipGroupBatchOptions &options,
                          const std::string &label,
                          util::Logger *log)
{
    PreparedBase result;
    std::vector<poly> raw_generators;
    result.generators.reserve(base.size());
    for (poly value : base)
        if (value)
            result.generators.push_back(p_Copy(value, R));

    if (!options.reuse_base_basis || result.generators.empty())
        return result;

    ideal source = nullptr;
    ideal basis = nullptr;
    try
    {
        if (options.membership.preprocess)
        {
            if (options.membership.verify_preprocess)
            {
                raw_generators.reserve(result.generators.size());
                for (poly value : result.generators)
                    raw_generators.push_back(value ? p_Copy(value, R) : nullptr);
            }
            std::vector<poly> no_targets;
            util::gb::GbPreprocessStats stats;
            util::gb::preprocess_groebner_inputs(
                result.generators, no_targets, R, label + "-base", stats, log);
            if (options.membership.verify_preprocess)
                membership_detail::verify_ideal_equality(
                    raw_generators, result.generators, R, label + "-base",
                    result.groebner, log);
        }

        source = membership_detail::ideal_from_owned_polys(result.generators, R);
        basis = membership_detail::timed_groebner(
            source, R, label + "-base", result.groebner, log);
        if (basis)
        {
            result.generators.reserve(static_cast<std::size_t>(IDELEMS(basis)));
            for (int i = 0; i < IDELEMS(basis); ++i)
                if (basis->m[i])
                    result.generators.push_back(p_Copy(basis->m[i], R));
            idDelete(&basis);
        }
        if (source)
            idDelete(&source);
        delete_polys(raw_generators, R);
        return result;
    }
    catch (...)
    {
        if (basis)
            idDelete(&basis);
        if (source)
            idDelete(&source);
        delete_polys(result.generators, R);
        delete_polys(raw_generators, R);
        throw;
    }
}

MembershipGroupBatchResult run_local(
    const std::vector<poly> &base_generators,
    const std::vector<MembershipGroup> &groups,
    ring R,
    const MembershipGroupBatchOptions &options,
    util::Logger *log)
{
    MembershipGroupBatchResult output;
    output.groups.reserve(groups.size());
    const std::string base_label = groups.empty() ? "gb-group" : groups.front().label;
    MembershipGroupBatchOptions effective_options = options;
    // A base GB is an amortization optimization, not a semantic requirement.
    // Small batches cannot recover its fixed cost and were substantially worse
    // in focused tests, so only construct it when at least eight ideals share
    // the same base in this worker.
    effective_options.reuse_base_basis =
        options.reuse_base_basis && !options.membership.ideal_rewrite &&
        groups.size() >= kBaseBasisMinGroups;
    effective_options.membership.return_normal_forms =
        options.return_normal_forms;
    const std::vector<poly> augmented_base =
        effective_options.reuse_base_basis
            ? base_with_common_group_generators(base_generators, groups, R)
            : base_generators;
    if (log && options.reuse_base_basis)
    {
        if (!effective_options.reuse_base_basis)
            LOG_INFO(*log, "singular",
                     "base-basis reuse skipped: groups=" +
                         std::to_string(groups.size()) +
                         " threshold=" +
                         std::to_string(kBaseBasisMinGroups));
        else
            LOG_INFO(*log, "singular",
                     "base-basis reuse enabled: groups=" +
                         std::to_string(groups.size()) +
                         " base-generators=" +
                         std::to_string(base_generators.size()) +
                         " common-extra-promoted=" +
                         std::to_string(augmented_base.size() -
                                        base_generators.size()));
    }
    PreparedBase base = prepare_base(
        augmented_base, R, effective_options, base_label, log);
    output.base_groebner = base.groebner;

    try
    {
        for (const MembershipGroup &group : groups)
        {
            std::vector<poly> generators;
            generators.reserve(base.generators.size() + group.extra_generators.size());
            generators.insert(generators.end(), base.generators.begin(), base.generators.end());
            generators.insert(generators.end(), group.extra_generators.begin(),
                              group.extra_generators.end());
            MembershipBatchResult result = prove_membership(
                generators, group.targets, R, effective_options.membership,
                group.label, log);
            output.groups.push_back(std::move(result));
        }
        delete_polys(base.generators, R);
        return output;
    }
    catch (...)
    {
        delete_polys(base.generators, R);
        throw;
    }
}

struct WirePoly
{
    bool present = false;
    std::string text;
};

void put_poly(ByteWriter &writer, const WirePoly &poly_value)
{
    writer.put_bool(poly_value.present);
    if (poly_value.present)
        writer.put_string(poly_value.text);
}

WirePoly get_wire_poly(ByteReader &reader)
{
    WirePoly value;
    value.present = reader.get_bool();
    if (value.present)
        value.text = reader.get_string();
    return value;
}

poly materialize_poly(const WirePoly &value, ring R)
{
    return value.present ? poly_from_wire(value.text, R) : nullptr;
}

struct SerializedGroup
{
    std::size_t index = 0;
    std::string label;
    std::vector<WirePoly> extra;
    std::vector<WirePoly> targets;
};

struct SerializedBatch
{
    std::vector<WirePoly> base;
    std::vector<SerializedGroup> groups;
};

WirePoly serialize_poly(poly value, ring R)
{
    WirePoly result;
    result.present = value != nullptr;
    if (result.present)
        result.text = poly_to_wire(value, R);
    return result;
}

SerializedBatch serialize_batch(const std::vector<poly> &base,
                                const std::vector<MembershipGroup> &groups,
                                ring R)
{
    SerializedBatch result;
    result.base.reserve(base.size());
    for (poly value : base)
        result.base.push_back(serialize_poly(value, R));
    result.groups.reserve(groups.size());
    for (std::size_t i = 0; i < groups.size(); ++i)
    {
        SerializedGroup group;
        group.index = i;
        group.label = groups[i].label;
        group.extra.reserve(groups[i].extra_generators.size());
        for (poly value : groups[i].extra_generators)
            group.extra.push_back(serialize_poly(value, R));
        group.targets.reserve(groups[i].targets.size());
        for (poly value : groups[i].targets)
            group.targets.push_back(serialize_poly(value, R));
        result.groups.push_back(std::move(group));
    }
    return result;
}

std::vector<std::uint8_t> encode_request(
    const SerializedBatch &batch,
    const std::vector<std::size_t> &group_indices,
    const MembershipGroupBatchOptions &options)
{
    ByteWriter writer;
    writer.put_u64(kProtocolVersion);
    writer.put_bool(options.membership.preprocess);
    writer.put_bool(options.membership.verify_preprocess);
    writer.put_bool(options.membership.ideal_rewrite);
    writer.put_bool(options.reuse_base_basis);
    writer.put_bool(options.return_normal_forms);
    writer.put_u64(batch.base.size());
    for (const WirePoly &value : batch.base)
        put_poly(writer, value);
    writer.put_u64(group_indices.size());
    for (std::size_t index : group_indices)
    {
        const SerializedGroup &group = batch.groups.at(index);
        writer.put_u64(group.index);
        writer.put_string(group.label);
        writer.put_u64(group.extra.size());
        for (const WirePoly &value : group.extra)
            put_poly(writer, value);
        writer.put_u64(group.targets.size());
        for (const WirePoly &value : group.targets)
            put_poly(writer, value);
    }
    return writer.data();
}

struct WorkerResponse
{
    bool ok = false;
    std::string error;
    std::vector<std::pair<std::size_t, MembershipBatchResult>> groups;
    GroebnerTiming base_groebner;
    RuntimeStatistics runtime;
    std::size_t max_rss_kb = 0;
};

void put_timing(ByteWriter &writer, const OperationTiming &timing)
{
    writer.put_u64(timing.calls);
    writer.put_u64(static_cast<std::uint64_t>(timing.elapsed.count()));
    writer.put_u64(timing.bytes);
}

OperationTiming get_timing(ByteReader &reader)
{
    OperationTiming result;
    result.calls = reader.get_u64();
    result.elapsed = std::chrono::nanoseconds(reader.get_u64());
    result.bytes = reader.get_u64();
    return result;
}

void put_runtime(ByteWriter &writer, const RuntimeStatistics &stats)
{
    put_timing(writer, stats.preprocess);
    put_timing(writer, stats.normal_form);
    put_timing(writer, stats.serialization);
    put_timing(writer, stats.deserialization);
    put_timing(writer, stats.process_wall);
    writer.put_u64(stats.process_batches);
    writer.put_u64(stats.worker_max_rss_kb);
}

RuntimeStatistics get_runtime(ByteReader &reader)
{
    RuntimeStatistics result;
    result.preprocess = get_timing(reader);
    result.normal_form = get_timing(reader);
    result.serialization = get_timing(reader);
    result.deserialization = get_timing(reader);
    result.process_wall = get_timing(reader);
    result.process_batches = reader.get_u64();
    result.worker_max_rss_kb = reader.get_u64();
    return result;
}

std::vector<std::uint8_t> encode_response(const WorkerResponse &response)
{
    ByteWriter writer;
    writer.put_u64(kProtocolVersion);
    writer.put_bool(response.ok);
    writer.put_string(response.error);
    writer.put_u64(response.base_groebner.calls);
    writer.put_u64(response.base_groebner.elapsed.count());
    writer.put_u64(response.groups.size());
    for (const auto &[index, result] : response.groups)
    {
        writer.put_u64(index);
        writer.put_u64(result.groebner.calls);
        writer.put_u64(result.groebner.elapsed.count());
        writer.put_bool(result.used_preprocess);
        writer.put_u64(result.membership.size());
        for (bool value : result.membership)
            writer.put_bool(value);
        writer.put_u64(result.normal_forms.size());
        for (const std::string &value : result.normal_forms)
            writer.put_string(value);
    }
    put_runtime(writer, response.runtime);
    writer.put_u64(response.max_rss_kb);
    return writer.data();
}

WorkerResponse decode_response(const std::vector<std::uint8_t> &frame)
{
    ByteReader reader(frame);
    if (reader.get_u64() != kProtocolVersion)
        throw std::runtime_error("GB process-pool response version mismatch");
    WorkerResponse response;
    response.ok = reader.get_bool();
    response.error = reader.get_string();
    response.base_groebner.calls = reader.get_u64();
    response.base_groebner.elapsed = std::chrono::nanoseconds(reader.get_u64());
    const std::size_t group_count = reader.get_u64();
    response.groups.reserve(group_count);
    for (std::size_t i = 0; i < group_count; ++i)
    {
        const std::size_t index = reader.get_u64();
        MembershipBatchResult result;
        result.groebner.calls = reader.get_u64();
        result.groebner.elapsed = std::chrono::nanoseconds(reader.get_u64());
        result.used_preprocess = reader.get_bool();
        const std::size_t membership_count = reader.get_u64();
        result.membership.reserve(membership_count);
        for (std::size_t j = 0; j < membership_count; ++j)
            result.membership.push_back(reader.get_bool());
        const std::size_t normal_count = reader.get_u64();
        result.normal_forms.reserve(normal_count);
        for (std::size_t j = 0; j < normal_count; ++j)
            result.normal_forms.push_back(reader.get_string());
        response.groups.emplace_back(index, std::move(result));
    }
    response.runtime = get_runtime(reader);
    response.max_rss_kb = reader.get_u64();
    if (!reader.done())
        throw std::runtime_error("trailing bytes in GB process-pool response");
    return response;
}

struct MaterializedRequest
{
    std::vector<poly> base;
    std::vector<std::size_t> indices;
    std::vector<MembershipGroup> groups;
    MembershipGroupBatchOptions options;
};

MaterializedRequest decode_request(const std::vector<std::uint8_t> &frame,
                                   ring R)
{
    ByteReader reader(frame);
    if (reader.get_u64() != kProtocolVersion)
        throw std::runtime_error("GB process-pool request version mismatch");
    MaterializedRequest request;
    request.options.membership.preprocess = reader.get_bool();
    request.options.membership.verify_preprocess = reader.get_bool();
    request.options.membership.ideal_rewrite = reader.get_bool();
    request.options.reuse_base_basis = reader.get_bool();
    request.options.return_normal_forms = reader.get_bool();
    try
    {
        const std::size_t base_count = reader.get_u64();
        request.base.reserve(base_count);
        for (std::size_t i = 0; i < base_count; ++i)
            request.base.push_back(materialize_poly(get_wire_poly(reader), R));
        const std::size_t group_count = reader.get_u64();
        request.indices.reserve(group_count);
        request.groups.reserve(group_count);
        for (std::size_t i = 0; i < group_count; ++i)
        {
            request.indices.push_back(reader.get_u64());
            request.groups.emplace_back();
            MembershipGroup &group = request.groups.back();
            group.label = reader.get_string();
            const std::size_t extra_count = reader.get_u64();
            group.extra_generators.reserve(extra_count);
            for (std::size_t j = 0; j < extra_count; ++j)
                group.extra_generators.push_back(
                    materialize_poly(get_wire_poly(reader), R));
            const std::size_t target_count = reader.get_u64();
            group.targets.reserve(target_count);
            for (std::size_t j = 0; j < target_count; ++j)
                group.targets.push_back(
                    materialize_poly(get_wire_poly(reader), R));
        }
        if (!reader.done())
            throw std::runtime_error("trailing bytes in GB process-pool request");
        return request;
    }
    catch (...)
    {
        delete_polys(request.base, R);
        for (MembershipGroup &group : request.groups)
        {
            delete_polys(group.extra_generators, R);
            delete_polys(group.targets, R);
        }
        throw;
    }
}

void delete_request(MaterializedRequest &request, ring R)
{
    delete_polys(request.base, R);
    for (MembershipGroup &group : request.groups)
    {
        delete_polys(group.extra_generators, R);
        delete_polys(group.targets, R);
    }
}

WorkerResponse execute_request(const std::vector<std::uint8_t> &frame, ring R)
{
    WorkerResponse response;
    const RuntimeStatistics before = runtime_statistics();
    const auto deserialize_started = clk::now();
    MaterializedRequest request;
    try
    {
        request = decode_request(frame, R);
        record_deserialization(
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - deserialize_started),
            frame.size());
        MembershipGroupBatchResult batch = prove_membership_groups_serial(
            request.base, request.groups, R, request.options, nullptr);
        response.ok = true;
        response.base_groebner = batch.base_groebner;
        for (std::size_t i = 0; i < batch.groups.size(); ++i)
            response.groups.emplace_back(request.indices.at(i),
                                         std::move(batch.groups[i]));
        delete_request(request, R);
    }
    catch (const std::exception &error)
    {
        delete_request(request, R);
        response.error = error.what();
    }
    catch (...)
    {
        delete_request(request, R);
        response.error = "unknown GB worker exception";
    }
    response.runtime = subtract_runtime_statistics(runtime_statistics(), before);
    response.max_rss_kb = current_process_max_rss_kb();
    return response;
}

[[noreturn]] void worker_loop(int fd, ring R)
{
    rChangeCurrRing(R);
    // Forked workers inherit the parent's replay counter. Disable worker-side
    // dumps to avoid multiple processes racing on identical replay paths.
    configure_dump({false, {}, nullptr});
    ByteWriter ready;
    ready.put_u64(kProtocolVersion);
    if (!send_frame(fd, ready.data()))
    {
        close(fd);
        _exit(2);
    }
    while (true)
    {
        std::vector<std::uint8_t> request;
        try
        {
            if (!receive_frame(fd, request))
                break;
            WorkerResponse response = execute_request(request, R);
            if (!send_frame(fd, encode_response(response)))
                break;
        }
        catch (...)
        {
            break;
        }
    }
    close(fd);
    _exit(0);
}

} // namespace

MembershipGroupBatchResult prove_membership_groups_serial(
    const std::vector<poly> &base_generators,
    const std::vector<MembershipGroup> &groups,
    ring R,
    const MembershipGroupBatchOptions &options,
    util::Logger *log)
{
    MembershipGroupBatchOptions serial_options = options;
    serial_options.processes = 0;
    return run_local(base_generators, groups, R, serial_options, log);
}

struct MembershipProcessPool::Impl
{
    struct Worker
    {
        pid_t pid = -1;
        int fd = -1;
    };

    ring R = nullptr;
    util::Logger *log = nullptr;
    std::vector<Worker> workers;
    std::mutex run_mutex;
    bool poisoned = false;

    Impl(ring requested_ring, std::size_t count, util::Logger *requested_log)
        : R(requested_ring), log(requested_log)
    {
        if (R == nullptr || count == 0)
            return;
        if (getCoeffType(R->cf) != n_Z)
            throw std::invalid_argument(
                "GB process pool requires an integer (n_Z) coefficient ring");
        rChangeCurrRing(R);
        workers.reserve(count);
        try
        {
            for (std::size_t i = 0; i < count; ++i)
            {
                int sockets[2] = {-1, -1};
                if (socketpair(AF_UNIX, SOCK_STREAM, 0, sockets) != 0)
                    throw std::runtime_error("socketpair failed for GB process pool: " +
                                             std::string(std::strerror(errno)));
                const pid_t pid = fork();
                if (pid < 0)
                {
                    close(sockets[0]);
                    close(sockets[1]);
                    throw std::runtime_error("fork failed for GB process pool: " +
                                             std::string(std::strerror(errno)));
                }
                if (pid == 0)
                {
                    close(sockets[0]);
                    for (const Worker &worker : workers)
                        if (worker.fd >= 0)
                            close(worker.fd);
                    worker_loop(sockets[1], R);
                }
                close(sockets[1]);
                std::vector<std::uint8_t> ready_frame;
                if (!receive_frame(sockets[0], ready_frame))
                {
                    close(sockets[0]);
                    int status = 0;
                    (void)waitpid(pid, &status, 0);
                    throw std::runtime_error(
                        "GB process-pool worker exited before ready handshake: status=" +
                        std::to_string(status));
                }
                ByteReader ready(ready_frame);
                if (ready.get_u64() != kProtocolVersion || !ready.done())
                {
                    close(sockets[0]);
                    int status = 0;
                    (void)waitpid(pid, &status, 0);
                    throw std::runtime_error(
                        "invalid GB process-pool ready handshake");
                }
                workers.push_back({pid, sockets[0]});
            }
        }
        catch (...)
        {
            shutdown();
            throw;
        }
        if (log)
            LOG_INFO(*log, "singular",
                     "GB process pool started: workers=" +
                         std::to_string(workers.size()));
    }

    ~Impl()
    {
        shutdown();
    }

    void shutdown()
    {
        for (Worker &worker : workers)
        {
            if (worker.fd >= 0)
            {
                close(worker.fd);
                worker.fd = -1;
            }
        }
        for (Worker &worker : workers)
        {
            if (worker.pid <= 0)
                continue;
            int status = 0;
            while (waitpid(worker.pid, &status, 0) < 0 && errno == EINTR)
            {
            }
            worker.pid = -1;
        }
        workers.clear();
    }

    MembershipGroupBatchResult run(
        const std::vector<poly> &base_generators,
        const std::vector<MembershipGroup> &groups,
        const MembershipGroupBatchOptions &options)
    {
        std::lock_guard<std::mutex> run_lock(run_mutex);
        if (groups.empty())
            return {};
        if (poisoned && options.processes != 0)
            throw std::runtime_error(
                "GB process pool is unavailable after an earlier worker failure");
        const std::size_t active = std::min(
            {options.processes, workers.size(), groups.size()});
        if (active == 0)
            return prove_membership_groups_serial(
                base_generators, groups, R, options, log);

        MembershipGroupBatchOptions worker_options = options;
        PreparedBase prepared_base;
        PolyVectorGuard prepared_base_guard(prepared_base.generators, R);
        const std::vector<poly> *wire_base = &base_generators;
        if (options.reuse_base_basis && !options.membership.ideal_rewrite &&
            groups.size() >= kBaseBasisMinGroups)
        {
            const std::vector<poly> augmented_base =
                base_with_common_group_generators(
                    base_generators, groups, R);
            prepared_base = prepare_base(
                augmented_base, R, options, groups.front().label, log);
            wire_base = &prepared_base.generators;
            // Compute the shared basis exactly once in the parent, then send
            // that equivalent generator set to every worker.
            worker_options.reuse_base_basis = false;
            if (log)
                LOG_INFO(*log, "singular",
                         "base-basis reuse enabled before process dispatch: groups=" +
                             std::to_string(groups.size()) +
                             " base-generators=" +
                             std::to_string(base_generators.size()) +
                             " common-extra-promoted=" +
                             std::to_string(augmented_base.size() -
                                            base_generators.size()));
        }
        else if (options.reuse_base_basis && log)
            LOG_INFO(*log, "singular",
                     "base-basis reuse skipped before process dispatch: groups=" +
                         std::to_string(groups.size()) +
                         " threshold=" +
                         std::to_string(kBaseBasisMinGroups));

        const auto serialization_started = clk::now();
        SerializedBatch serialized = serialize_batch(*wire_base, groups, R);
        std::vector<std::vector<std::size_t>> assignments(active);
        for (std::size_t i = 0; i < groups.size(); ++i)
            assignments[i % active].push_back(i);
        std::vector<std::vector<std::uint8_t>> requests;
        requests.reserve(active);
        std::uint64_t request_bytes = 0;
        const auto process_wall_started = clk::now();
        for (std::size_t i = 0; i < active; ++i)
        {
            requests.push_back(
                encode_request(serialized, assignments[i], worker_options));
            request_bytes += requests.back().size();
        }
        record_serialization(
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - serialization_started),
            request_bytes);
        record_process_batch();

        MembershipGroupBatchResult output;
        output.base_groebner = prepared_base.groebner;
        output.groups.resize(groups.size());
        std::vector<bool> received(groups.size(), false);
        try
        {
            for (std::size_t i = 0; i < active; ++i)
            {
                if (send_frame(workers[i].fd, requests[i]))
                    continue;
                const int send_error = errno;
                int status = 0;
                const pid_t waited =
                    waitpid(workers[i].pid, &status, WNOHANG);
                std::string detail = std::strerror(send_error);
                if (waited == workers[i].pid)
                {
                    workers[i].pid = -1;
                    detail += " worker-status=" + std::to_string(status);
                }
                throw std::runtime_error(
                    "failed to send GB process-pool request: " + detail);
            }

            for (std::size_t i = 0; i < active; ++i)
            {
                std::vector<std::uint8_t> response_frame;
                if (!receive_frame(workers[i].fd, response_frame))
                    throw std::runtime_error(
                        "failed to receive GB process-pool response");
                WorkerResponse response = decode_response(response_frame);
                if (!response.ok)
                    throw std::runtime_error(
                        "GB worker failed: " + response.error);
                output.base_groebner.calls += response.base_groebner.calls;
                output.base_groebner.elapsed += response.base_groebner.elapsed;
                for (auto &[index, result] : response.groups)
                {
                    if (index >= output.groups.size() || received[index])
                        throw std::runtime_error(
                            "invalid duplicate GB worker group result");
                    received[index] = true;
                    output.groups[index] = std::move(result);
                }
                merge_runtime_statistics(response.runtime);
                record_worker_max_rss_kb(response.max_rss_kb);
            }
            if (std::find(received.begin(), received.end(), false) !=
                received.end())
                throw std::runtime_error("missing GB worker group result");
        }
        catch (...)
        {
            record_process_wall(
                std::chrono::duration_cast<std::chrono::nanoseconds>(
                    clk::now() - process_wall_started));
            poisoned = true;
            shutdown();
            throw;
        }
        if (options.membership.verify_preprocess)
        {
            MembershipGroupBatchOptions reference_options = options;
            reference_options.processes = 0;
            MembershipGroupBatchResult reference =
                prove_membership_groups_serial(
                    base_generators, groups, R, reference_options, log);
            if (reference.groups.size() != output.groups.size())
                throw std::runtime_error(
                    "GB process-pool serial verification group mismatch");
            output.base_groebner.calls += reference.base_groebner.calls;
            output.base_groebner.elapsed += reference.base_groebner.elapsed;
            for (std::size_t i = 0; i < output.groups.size(); ++i)
            {
                if (reference.groups[i].membership !=
                    output.groups[i].membership)
                    throw std::runtime_error(
                        "GB process-pool serialization verification failed for group " +
                        std::to_string(i));
                if (reference.groups[i].used_preprocess !=
                    output.groups[i].used_preprocess)
                    throw std::runtime_error(
                        "GB process-pool preprocess metadata mismatch for group " +
                        std::to_string(i));
                if (options.return_normal_forms &&
                    reference.groups[i].normal_forms !=
                        output.groups[i].normal_forms)
                    throw std::runtime_error(
                        "GB process-pool normal-form serialization mismatch for group " +
                        std::to_string(i));
                output.groups[i].groebner.calls +=
                    reference.groups[i].groebner.calls;
                output.groups[i].groebner.elapsed +=
                    reference.groups[i].groebner.elapsed;
            }
            if (log)
                LOG_INFO(*log, "singular",
                         "GB process-pool serialization verification OK: groups=" +
                             std::to_string(groups.size()));
        }
        record_process_wall(
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                clk::now() - process_wall_started));

        if (log)
        {
            if (output.base_groebner.calls != 0)
                LOG_INFO(*log, "singular",
                         "parallel base Groebner basis calls=" +
                             std::to_string(output.base_groebner.calls) +
                             " aggregate=" +
                             util::fmt_duration(output.base_groebner.elapsed));
            for (std::size_t i = 0; i < groups.size(); ++i)
                LOG_INFO(*log, "singular",
                         "Groebner basis std [" + groups[i].label +
                             "] finished in " +
                             util::fmt_duration(output.groups[i].groebner.elapsed) +
                             " (GB worker process)");
        }
        return output;
    }
};

MembershipProcessPool::MembershipProcessPool(ring R, std::size_t workers,
                                             util::Logger *log)
    : m_impl(std::make_unique<Impl>(R, workers, log))
{
}

MembershipProcessPool::~MembershipProcessPool() = default;

std::size_t MembershipProcessPool::workers() const
{
    return m_impl ? m_impl->workers.size() : 0;
}

MembershipGroupBatchResult MembershipProcessPool::run(
    const std::vector<poly> &base_generators,
    const std::vector<MembershipGroup> &groups,
    const MembershipGroupBatchOptions &options)
{
    if (!m_impl)
        throw std::runtime_error("GB process pool is not initialized");
    return m_impl->run(base_generators, groups, options);
}

} // namespace util::singular
