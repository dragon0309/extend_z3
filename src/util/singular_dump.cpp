#include "util/singular_dump.hpp"

#include <algorithm>
#include <atomic>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <mutex>
#include <sstream>
#include <unordered_map>
#include <utility>
#include <vector>

namespace util::singular
{
namespace
{

struct Replay
{
    std::filesystem::path path;
    std::string label;
    std::string ring_declaration;
    std::vector<std::string> input_generators;
    std::vector<std::string> result_generators;
    std::vector<std::pair<std::string, std::string>> normal_forms;
    bool computes_groebner = true;
};

struct Recorder
{
    DumpConfig config;
    std::atomic<std::uint64_t> next_id{1};
    std::mutex mutex;
    std::unordered_map<ideal, Replay> basis_replays;
};

Recorder &recorder()
{
    static Recorder value;
    return value;
}

void log_message(const std::string &message)
{
    util::Logger *logger = recorder().config.logger;
    if (logger)
        LOG_INFO(*logger, "singular-dump", message);
}

std::string sanitize_label(std::string label)
{
    for (char &ch : label)
        if (!(std::isalnum(static_cast<unsigned char>(ch)) || ch == '_' || ch == '-'))
            ch = '_';
    while (!label.empty() && label.back() == '_')
        label.pop_back();
    if (label.empty())
        label = "call";
    constexpr std::size_t max_length = 80;
    if (label.size() > max_length)
        label.resize(max_length);
    return label;
}

std::string term_to_string(poly term, ring R)
{
    number coefficient = n_Copy(p_GetCoeff(term, R), R->cf);
    poly copy = p_NSet(coefficient, R);
    for (int i = 1; i <= R->N; ++i)
    {
        const long exponent = p_GetExp(term, i, R);
        if (exponent != 0)
            p_SetExp(copy, i, exponent, R);
    }
    const long component = p_GetComp(term, R);
    if (component != 0)
        p_SetComp(copy, component, R);
    p_Setm(copy, R);

    char *raw = p_String(copy, R);
    std::string result = raw ? std::string(raw) : std::string("0");
    if (raw)
        omFree(raw);
    p_Delete(&copy, R);
    return result;
}

std::string poly_to_string(poly value, ring R)
{
    if (!value)
        return "0";

    std::ostringstream out;
    bool first = true;
    for (poly term = value; term; term = pNext(term))
    {
        const std::string text = term_to_string(term, R);
        if (!first && !text.empty() && text.front() != '-')
            out << '+';
        out << text;
        first = false;
    }
    return first ? std::string("0") : out.str();
}

std::vector<std::string> ideal_to_strings(ideal value, ring R)
{
    std::vector<std::string> result;
    if (!value)
        return result;
    result.reserve(static_cast<std::size_t>(IDELEMS(value)));
    for (int i = 0; i < IDELEMS(value); ++i)
        result.push_back(poly_to_string(value->m[i], R));
    return result;
}

std::string ordering_name(ring R)
{
    if (R && R->order)
    {
        if (R->order[0] == ringorder_dp)
            return "dp";
        if (R->order[0] == ringorder_Dp)
            return "Dp";
        if (R->order[0] == ringorder_rp)
            return "rp";
    }
    return "lp";
}

std::string ring_declaration(ring R)
{
    std::ostringstream out;
    out << "ring r = integer, (";
    for (int i = 0; i < R->N; ++i)
    {
        if (i)
            out << ',';
        out << (R->names && R->names[i] ? R->names[i] : "x" + std::to_string(i + 1));
    }
    out << "), " << ordering_name(R) << ";";
    return out.str();
}

void write_ideal(std::ostream &out,
                 const std::string &name,
                 const std::vector<std::string> &generators)
{
    out << "ideal " << name << " = ";
    if (generators.empty())
    {
        out << "0;\n";
        return;
    }
    out << "\n";
    for (std::size_t i = 0; i < generators.size(); ++i)
        out << "  " << generators[i] << (i + 1 == generators.size() ? ";\n" : ",\n");
}

bool write_replay(const Replay &replay)
{
    const std::filesystem::path temporary = replay.path.string() + ".tmp";
    std::ofstream out(temporary, std::ios::out | std::ios::trunc);
    if (!out)
    {
        log_message("failed to open temporary replay file: " + temporary.string());
        return false;
    }

    out << "// Generated from the actual libSingular inputs used by main.\n";
    if (!replay.label.empty())
        out << "// Label: " << replay.label << "\n";
    out << replay.ring_declaration << "\n";
    if (replay.computes_groebner)
    {
        write_ideal(out, "I", replay.input_generators);
        out << "ideal G = std(I);\n";
        out << "\"// Groebner basis\";\nG;\n";
    }
    else
    {
        // This mirrors a direct kNF call whose basis was not produced through
        // this module; do not silently introduce an extra std() calculation.
        write_ideal(out, "G", replay.input_generators);
    }
    if (!replay.result_generators.empty())
    {
        out << "\n// Basis returned by libSingular in the recorded run.\n";
        write_ideal(out, "expected_G", replay.result_generators);
    }

    for (std::size_t i = 0; i < replay.normal_forms.size(); ++i)
    {
        const std::size_t index = i + 1;
        out << "\npoly target_" << index << " = " << replay.normal_forms[i].first << ";\n";
        out << "poly nf_" << index << " = reduce(target_" << index << ", G);\n";
        out << "\"// Normal form " << index << "\";\nnf_" << index << ";\n";
        out << "poly expected_nf_" << index << " = " << replay.normal_forms[i].second << ";\n";
    }
    out.close();
    if (!out)
    {
        log_message("failed while writing replay file: " + temporary.string());
        return false;
    }

    std::error_code ec;
    std::filesystem::rename(temporary, replay.path, ec);
    if (ec)
    {
        std::filesystem::remove(replay.path, ec);
        ec.clear();
        std::filesystem::rename(temporary, replay.path, ec);
    }
    if (ec)
    {
        log_message("failed to publish replay file " + replay.path.string() + ": " + ec.message());
        return false;
    }
    return true;
}

std::filesystem::path allocate_path(const std::string &kind, const std::string &label)
{
    Recorder &state = recorder();
    const std::uint64_t id = state.next_id.fetch_add(1, std::memory_order_relaxed);
    std::ostringstream name;
    name << std::setfill('0') << std::setw(6) << id << '-' << kind << '-'
         << sanitize_label(label) << ".sing";
    return std::filesystem::path(state.config.output_dir) / name.str();
}

bool ensure_output_directory()
{
    std::error_code ec;
    std::filesystem::create_directories(recorder().config.output_dir, ec);
    if (ec)
    {
        log_message("failed to create dump directory " + recorder().config.output_dir + ": " +
                    ec.message());
        return false;
    }
    return true;
}

std::uint64_t next_available_id()
{
    std::uint64_t greatest = 0;
    std::error_code ec;
    for (const auto &entry : std::filesystem::directory_iterator(recorder().config.output_dir, ec))
    {
        if (ec)
            break;
        const std::string name = entry.path().filename().string();
        const std::size_t dash = name.find('-');
        if (dash == std::string::npos || dash == 0)
            continue;
        if (!std::all_of(name.begin(), name.begin() + static_cast<std::ptrdiff_t>(dash),
                         [](unsigned char ch) { return std::isdigit(ch) != 0; }))
            continue;
        try
        {
            greatest = std::max(greatest,
                                static_cast<std::uint64_t>(std::stoull(name.substr(0, dash))));
        }
        catch (const std::exception &)
        {
        }
    }
    return greatest + 1;
}

} // namespace

void configure_dump(DumpConfig config)
{
    Recorder &state = recorder();
    std::lock_guard<std::mutex> lock(state.mutex);
    state.config = std::move(config);
    state.basis_replays.clear();
    if (state.config.enabled)
    {
        if (ensure_output_directory())
            state.next_id.store(next_available_id(), std::memory_order_relaxed);
    }
    else
    {
        state.next_id.store(1, std::memory_order_relaxed);
    }
}

bool dump_enabled()
{
    return recorder().config.enabled;
}

ideal groebner(ideal input, ring R, const std::string &label)
{
    rChangeCurrRing(R);
    Recorder &state = recorder();
    const bool enabled = state.config.enabled;
    const std::string ring_text = enabled ? ring_declaration(R) : std::string();
    const std::vector<std::string> input_text =
        enabled ? ideal_to_strings(input, R) : std::vector<std::string>();

    intvec *weights_value = nullptr;
    intvec **weights = &weights_value;
    ideal result = kStd(input, nullptr, testHomog, weights, nullptr, 0, 0, nullptr);

    if (!enabled)
        return result;

    std::lock_guard<std::mutex> lock(state.mutex);
    if (!ensure_output_directory())
        return result;

    Replay replay;
    replay.path = allocate_path("gb", label);
    replay.label = label;
    replay.ring_declaration = ring_text;
    replay.input_generators = input_text;
    replay.result_generators = ideal_to_strings(result, R);
    if (write_replay(replay))
        log_message("wrote Singular replay: " + replay.path.string());
    if (result)
        state.basis_replays[result] = std::move(replay);
    return result;
}

poly normal_form(ideal basis, poly target, ring R, const std::string &label)
{
    rChangeCurrRing(R);
    const bool enabled = recorder().config.enabled;
    const std::string target_text = enabled ? poly_to_string(target, R) : std::string();
    const std::string ring_text = enabled ? ring_declaration(R) : std::string();
    const std::vector<std::string> basis_text =
        enabled ? ideal_to_strings(basis, R) : std::vector<std::string>();
    poly result = kNF(basis, nullptr, target, 0, 0);
    if (!enabled)
        return result;

    Recorder &state = recorder();
    std::lock_guard<std::mutex> lock(state.mutex);
    if (!ensure_output_directory())
        return result;

    auto found = state.basis_replays.find(basis);
    if (found != state.basis_replays.end())
    {
        found->second.normal_forms.emplace_back(target_text, poly_to_string(result, R));
        if (!write_replay(found->second))
            log_message("could not update Singular replay: " + found->second.path.string());
        return result;
    }

    Replay replay;
    replay.path = allocate_path("nf", label);
    replay.label = label;
    replay.ring_declaration = ring_text;
    // A standalone NF replay receives the already-computed basis as G.
    replay.input_generators = basis_text;
    replay.result_generators = replay.input_generators;
    replay.normal_forms.emplace_back(target_text, poly_to_string(result, R));
    replay.computes_groebner = false;
    if (write_replay(replay))
        log_message("wrote standalone Singular NF replay: " + replay.path.string());
    return result;
}

ideal lift(ideal source,
           ideal submodule,
           ideal *remainder,
           ring R,
           const std::string &label)
{
    rChangeCurrRing(R);
    Recorder &state = recorder();
    const bool enabled = state.config.enabled;
    const std::string ring_text = enabled ? ring_declaration(R) : std::string();
    const std::vector<std::string> source_text =
        enabled ? ideal_to_strings(source, R) : std::vector<std::string>();
    const std::vector<std::string> submodule_text =
        enabled ? ideal_to_strings(submodule, R) : std::vector<std::string>();

    ideal result = idLift(source, submodule, remainder, FALSE, FALSE, FALSE, nullptr, GbDefault);
    rChangeCurrRing(R);

    if (!enabled)
        return result;
    std::lock_guard<std::mutex> lock(state.mutex);
    if (!ensure_output_directory())
        return result;

    Replay replay;
    replay.path = allocate_path("lift", label);
    replay.label = label;
    replay.ring_declaration = ring_text;

    const std::filesystem::path temporary = replay.path.string() + ".tmp";
    std::ofstream out(temporary, std::ios::out | std::ios::trunc);
    if (!out)
    {
        log_message("failed to open lift replay: " + temporary.string());
        return result;
    }
    out << "// Generated from the actual libSingular inputs used by main.\n";
    if (!label.empty())
        out << "// Label: " << label << "\n";
    out << replay.ring_declaration << "\n";
    write_ideal(out, "I", source_text);
    write_ideal(out, "T", submodule_text);
    out << "matrix certificate = lift(I, T);\ncertificate;\n";
    if (result)
        write_ideal(out, "expected_certificate", ideal_to_strings(result, R));
    if (remainder && *remainder)
        write_ideal(out, "expected_remainder", ideal_to_strings(*remainder, R));
    out.close();

    std::error_code ec;
    std::filesystem::rename(temporary, replay.path, ec);
    if (ec)
    {
        std::filesystem::remove(replay.path, ec);
        ec.clear();
        std::filesystem::rename(temporary, replay.path, ec);
    }
    if (ec)
        log_message("failed to publish lift replay " + replay.path.string() + ": " + ec.message());
    else
        log_message("wrote Singular lift replay: " + replay.path.string());
    return result;
}

} // namespace util::singular
