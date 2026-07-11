#include "util/bv_eq.hpp"

#include <algorithm>
#include <chrono>
#include <map>
#include <memory>
#include <optional>
#include <stdexcept>
#include <thread>
#include <unordered_set>

#include "util/fmt_duration.hpp"

namespace util::bveq
{

using namespace z3;
using clk = std::chrono::steady_clock;


static bool is_bv_to_int_app(const expr &e)
{
    if (!e.is_app() || !e.get_sort().is_int() || e.num_args() != 1 ||
        !e.arg(0).get_sort().is_bv())
        return false;
#ifdef Z3_OP_BV2INT
    if (e.decl().decl_kind() == Z3_OP_BV2INT)
        return true;
#endif
    const std::string n = e.decl().name().str();
    return n == "ubv_to_int" || n == "sbv_to_int" ||
           n == "bv2nat" || n == "bv2int";
}

static void collect_coeff_bases_rec(const expr &e, std::unordered_set<Z3_ast> &out)
{
    if (e.get_sort().is_int())
    {
        if (e.is_const() && !e.is_numeral())
            out.insert((Z3_ast)e);
        else if (is_bv_to_int_app(e))
            out.insert((Z3_ast)e);
    }
    if (!e.is_app())
        return;
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_coeff_bases_rec(e.arg(i), out);
}

void collect_bv_constants(const expr &e, std::unordered_set<Z3_ast> &out)
{
    if (e.is_const() && e.get_sort().is_bv() && !e.is_numeral())
        out.insert((Z3_ast)e);
    if (!e.is_app())
        return;
    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_bv_constants(e.arg(i), out);
}

bool assertion_contains_poly(const expr &e)
{
    if (!e.is_app())
        return false;
    const std::string name = e.decl().name().str();
    if (name == "eqP" || name == "eqmodP1" || name == "eqmodP2" ||
        name == "PConst" || name == "PVar" || name == "PNeg" ||
        name == "PAdd" || name == "PSub" || name == "PMul" || name == "PPow")
        return true;
    for (unsigned i = 0; i < e.num_args(); ++i)
        if (assertion_contains_poly(e.arg(i)))
            return true;
    return false;
}

struct ParallelBvEqCandidateInput
{
    std::unique_ptr<context> ctx;
    std::vector<expr> constraints;
    std::vector<expr> terms;
    std::optional<unsigned> seed;
};

struct ParallelBvEqCandidateResult
{
    check_result status = unknown;
    std::vector<IndexedCandidate> candidates;
    std::vector<std::string> model_values;
    std::chrono::nanoseconds elapsed{0};
    std::string error;
};

static ParallelBvEqCandidateInput make_parallel_bv_eq_candidate_input(
    context &source_ctx,
    const std::vector<expr> &constraints,
    const std::vector<expr> &terms,
    std::optional<unsigned> seed)
{
    ParallelBvEqCandidateInput input;
    input.ctx = std::make_unique<context>();
    input.constraints.reserve(constraints.size());
    input.terms.reserve(terms.size());
    for (const expr &constraint : constraints)
        input.constraints.emplace_back(
            *input.ctx,
            Z3_translate((Z3_context)source_ctx, (Z3_ast)constraint,
                         (Z3_context)*input.ctx));
    for (const expr &term : terms)
        input.terms.emplace_back(
            *input.ctx,
            Z3_translate((Z3_context)source_ctx, (Z3_ast)term,
                         (Z3_context)*input.ctx));
    input.seed = seed;
    return input;
}

static void run_parallel_bv_eq_candidate_worker(
    ParallelBvEqCandidateInput &input,
    ParallelBvEqCandidateResult &result)
{
    const auto started = clk::now();
    try
    {
        solver candidate_solver(*input.ctx);
        candidate_solver.set("timeout", 30000u);
        if (input.seed)
            candidate_solver.set("random_seed", *input.seed);
        for (const expr &constraint : input.constraints)
            candidate_solver.add(constraint);

        CallbackCandidateCollector collector(&candidate_solver, input.terms);
        result.status = candidate_solver.check();
        if (result.status == sat)
        {
            model candidate_model = candidate_solver.get_model();
            result.model_values.reserve(input.terms.size());
            for (const expr &term : input.terms)
                result.model_values.push_back(candidate_model.eval(term, true).to_string());
            result.candidates = collector.export_indexed_candidates();
        }
    }
    catch (const std::exception &ex)
    {
        result.error = ex.what();
    }
    catch (...)
    {
        result.error = "unknown exception in parallel BV equality candidate worker";
    }
    result.elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
        clk::now() - started);
}

Result prove(
    context &ctx,
    const std::vector<expr> &asserts,
    const Options &options,
    util::Logger &log)
{
    Result result;
    std::vector<expr> bv_constraints;
    for (const expr &a : asserts)
        if (!assertion_contains_poly(a))
            bv_constraints.push_back(a);

    std::unordered_set<Z3_ast> base_set;
    for (const expr &a : asserts)
        collect_coeff_bases_rec(a, base_set);

    struct BvInfo
    {
        expr bv_term;
        std::string conv_func;
        unsigned bv_width;
    };
    std::vector<BvInfo> ring_bv;

    for (Z3_ast ast : base_set)
    {
        expr base(ctx, ast);
        if (!is_bv_to_int_app(base))
            continue;
        expr bv = base.arg(0);
        if (!bv.is_const() || bv.is_numeral())
            continue;
        ring_bv.push_back({bv, base.decl().name().str(), bv.get_sort().bv_size()});
    }

    if (ring_bv.size() < 2)
        return result;

    std::unordered_set<std::string> proved_keys;
    auto record_proved = [&](const std::string &conv,
                             std::string a,
                             std::string b,
                             const std::string &label) -> bool
    {
        if (b < a)
            std::swap(a, b);
        const std::string key = conv + ":" + a + ":" + b;
        if (!proved_keys.insert(key).second)
            return false;
        LOG_INFO(log, "bveq",
                 "[bv-eq-prover] " + label + ": " + a + " == " + b);
        result.equalities.push_back({conv, a, b});
        return true;
    };

    LOG_INFO(log, "bveq",
             "[bv-eq-prover] " + std::to_string(ring_bv.size()) +
                 " ring-mapped BV variable(s), " +
                 std::to_string(bv_constraints.size()) + " BV constraint(s)");

    std::vector<expr> callback_terms;
    std::unordered_set<Z3_ast> callback_term_set;
    for (const BvInfo &info : ring_bv)
        if (callback_term_set.insert((Z3_ast)info.bv_term).second)
            callback_terms.push_back(info.bv_term);
    if (options.all_bv_constants)
    {
        std::unordered_set<Z3_ast> all_bv_constants;
        for (const expr &a : asserts)
            collect_bv_constants(a, all_bv_constants);
        for (Z3_ast ast : all_bv_constants)
            if (callback_term_set.insert(ast).second)
                callback_terms.emplace_back(ctx, ast);
    }
    LOG_INFO(log, "bveq",
             "[bv-eq-prover] registered " +
                 std::to_string(callback_terms.size()) +
                 " BV callback term(s), mode=" +
                 std::string(options.all_bv_constants
                                 ? "all-bv-constants"
                                 : "ring-mapped-only"));

    solver candidate_solver(ctx);
    candidate_solver.set("timeout", 30000u);
    for (const expr &constraint : bv_constraints)
        candidate_solver.add(constraint);
    CallbackCandidateCollector collector(&candidate_solver, callback_terms);
    LOG_INFO(log, "bveq",
             "[bv-eq-prover] seeded candidate solver(s)=" +
                 std::to_string(options.seeded_candidate_solvers));
    const auto candidate_search_t0 = clk::now();
    check_result candidate_result = unknown;
    std::vector<model> candidate_models;
    std::vector<std::vector<std::string>> parallel_candidate_model_values;
    if (options.parallel_candidates)
    {
        const std::size_t worker_count = options.seeded_candidate_solvers + 1;
        LOG_INFO(log, "bveq",
                 "[bv-eq-prover] candidate search mode=parallel, workers=" +
                     std::to_string(worker_count));

        std::vector<ParallelBvEqCandidateInput> inputs;
        inputs.reserve(worker_count);
        inputs.push_back(make_parallel_bv_eq_candidate_input(
            ctx, bv_constraints, callback_terms, std::nullopt));
        for (std::size_t seed = 1; seed <= options.seeded_candidate_solvers; ++seed)
            inputs.push_back(make_parallel_bv_eq_candidate_input(
                ctx, bv_constraints, callback_terms, static_cast<unsigned>(seed)));

        std::vector<ParallelBvEqCandidateResult> results(worker_count);
        std::vector<std::jthread> workers;
        workers.reserve(worker_count);
        for (std::size_t i = 0; i < worker_count; ++i)
            workers.emplace_back(run_parallel_bv_eq_candidate_worker,
                                 std::ref(inputs[i]), std::ref(results[i]));
        for (std::jthread &worker : workers)
            worker.join();

        for (std::size_t i = 0; i < results.size(); ++i)
        {
            const std::string worker_label =
                i == 0 ? "default" : "seed=" + std::to_string(i);
            LOG_INFO(log, "bveq",
                     "[bv-eq-prover] candidate worker " + worker_label +
                         ": status=" +
                         std::string(results[i].status == sat
                                         ? "sat"
                                         : results[i].status == unsat ? "unsat" : "unknown") +
                         ", candidates=" + std::to_string(results[i].candidates.size()) +
                         ", time=" + util::fmt_duration(results[i].elapsed));
            if (!results[i].error.empty())
                throw std::runtime_error(
                    "parallel BV equality candidate worker " +
                    std::to_string(i) + " failed: " + results[i].error);
        }

        candidate_result = results.front().status;
        if (candidate_result == sat)
        {
            for (const ParallelBvEqCandidateResult &result : results)
            {
                if (result.status != sat)
                    continue;
                collector.merge_indexed_candidates(callback_terms, result.candidates);
                parallel_candidate_model_values.push_back(result.model_values);
            }
        }
    }
    else
    {
        LOG_INFO(log, "bveq", "[bv-eq-prover] candidate search mode=sequential");
        candidate_result = candidate_solver.check();
        if (candidate_result == sat)
        {
            candidate_models.push_back(candidate_solver.get_model());
            for (std::size_t seed = 1; seed <= options.seeded_candidate_solvers; ++seed)
            {
                solver seeded_candidate_solver(ctx);
                seeded_candidate_solver.set("timeout", 30000u);
                seeded_candidate_solver.set("random_seed", static_cast<unsigned>(seed));
                for (const expr &constraint : bv_constraints)
                    seeded_candidate_solver.add(constraint);
                CallbackCandidateCollector seeded_collector(&seeded_candidate_solver,
                                                                callback_terms);
                if (seeded_candidate_solver.check() == sat)
                {
                    candidate_models.push_back(seeded_candidate_solver.get_model());
                    collector.merge(seeded_collector);
                }
            }
        }
    }
    const auto candidate_search_t1 = clk::now();

    if (candidate_result == sat && !collector.candidates().empty())
    {
        LOG_INFO(log, "bveq",
                 "[bv-eq-prover] BV eq candidates=" +
                     std::to_string(collector.candidates().size()));

        std::unordered_map<Z3_ast, std::vector<std::size_t>> views_by_bv;
        for (std::size_t i = 0; i < ring_bv.size(); ++i)
            views_by_bv[(Z3_ast)ring_bv[i].bv_term].push_back(i);

        // Do not spend a validity check on callback pairs that cannot produce
        // a polynomial generator.  In particular, unsigned and signed
        // BV-to-Int views are intentionally kept in separate equality graphs.
        auto has_compatible_views = [&](std::size_t candidate_idx)
        {
            const auto &[x, y] = collector.candidates()[candidate_idx];
            auto xi = views_by_bv.find((Z3_ast)x);
            auto yi = views_by_bv.find((Z3_ast)y);
            if (xi == views_by_bv.end() || yi == views_by_bv.end())
                return false;
            for (std::size_t lhs_idx : xi->second)
                for (std::size_t rhs_idx : yi->second)
                    if (ring_bv[lhs_idx].bv_width == ring_bv[rhs_idx].bv_width &&
                        ring_bv[lhs_idx].conv_func == ring_bv[rhs_idx].conv_func)
                        return true;
            return false;
        };

        std::size_t checks = 0;
        std::size_t discovered = 0;

        using ModelValues = std::unordered_map<Z3_ast, std::string>;
        auto evaluate_terms = [&](const model &m)
        {
            ModelValues values;
            values.reserve(callback_terms.size());
            for (const expr &term : callback_terms)
                values.emplace((Z3_ast)term, m.eval(term, true).to_string());
            return values;
        };
        auto agrees_with_values = [&](const ModelValues &values,
                                      std::size_t candidate_idx)
        {
            const auto &[x, y] = collector.candidates()[candidate_idx];
            auto xv = values.find((Z3_ast)x);
            auto yv = values.find((Z3_ast)y);
            return xv != values.end() && yv != values.end() && xv->second == yv->second;
        };

        std::vector<ModelValues> candidate_model_values;
        candidate_model_values.reserve(candidate_models.size() +
                                       parallel_candidate_model_values.size());
        for (const model &candidate_model : candidate_models)
            candidate_model_values.push_back(evaluate_terms(candidate_model));
        for (const std::vector<std::string> &values : parallel_candidate_model_values)
        {
            if (values.size() != callback_terms.size())
                throw std::runtime_error("parallel BV equality candidate model has wrong size");
            ModelValues mapped_values;
            mapped_values.reserve(values.size());
            for (std::size_t i = 0; i < values.size(); ++i)
                mapped_values.emplace((Z3_ast)callback_terms[i], values[i]);
            candidate_model_values.push_back(std::move(mapped_values));
        }
        std::vector<std::size_t> work_queue;
        for (std::size_t i = 0; i < collector.candidates().size(); ++i)
        {
            if (!has_compatible_views(i))
                continue;
            bool agrees_with_all_models = true;
            for (const ModelValues &values : candidate_model_values)
                if (!agrees_with_values(values, i))
                {
                    agrees_with_all_models = false;
                    break;
                }
            if (agrees_with_all_models)
                work_queue.push_back(i);
        }
        std::sort(work_queue.begin(), work_queue.end(),
                  [&](std::size_t a, std::size_t b)
                  {
                      if (collector.candidate_depth(a) != collector.candidate_depth(b))
                          return collector.candidate_depth(a) > collector.candidate_depth(b);
                      return collector.candidate_count(a) < collector.candidate_count(b);
                  });
        LOG_INFO(log, "bveq",
                 "[bv-eq-prover] model-compatible candidates=" +
                     std::to_string(work_queue.size()));
        LOG_INFO(log, "bveq",
                 "[bv-eq-prover] validation batch size=" +
                     std::to_string(options.validation_batch_size));

        std::size_t validation_batch_size = options.validation_batch_size;
        const auto validation_t0 = clk::now();
        while (!work_queue.empty())
        {
            const std::size_t batch_size =
                std::min(validation_batch_size, work_queue.size());
            std::vector<std::size_t> batch;
            batch.reserve(batch_size);
            for (std::size_t i = 0; i < batch_size; ++i)
            {
                batch.push_back(work_queue.back());
                work_queue.pop_back();
            }

            // A single UNSAT result for the disjunction proves every equality
            // in the batch.  A SAT model still prunes all callback candidates
            // that it separates, just as in the former one-pair-at-a-time loop.
            solver validator(ctx);
            validator.set("timeout", 10000u);
            for (const expr &constraint : bv_constraints)
                validator.add(constraint);
            expr_vector differences(ctx);
            for (std::size_t candidate_idx : batch)
            {
                const auto &[x, y] = collector.candidates()[candidate_idx];
                differences.push_back(x != y);
            }
            validator.add(mk_or(differences));
            ++checks;
            check_result r = validator.check();
            if (r == sat)
            {
                model counterexample = validator.get_model();
                const ModelValues counterexample_values = evaluate_terms(counterexample);
                std::vector<std::size_t> survivors;
                survivors.reserve(work_queue.size() + batch.size());
                for (std::size_t i : work_queue)
                    if (agrees_with_values(counterexample_values, i))
                        survivors.push_back(i);
                for (std::size_t i : batch)
                    if (agrees_with_values(counterexample_values, i))
                        survivors.push_back(i);
                work_queue.swap(survivors);
                validation_batch_size = options.validation_batch_size;
                continue;
            }
            if (r == unknown)
            {
                // Retry a smaller disjunction.  At size one this is the old
                // per-candidate behavior, so an isolated timeout is skipped
                // without blocking other candidates.
                if (batch.size() > 1)
                {
                    work_queue.insert(work_queue.end(), batch.begin(), batch.end());
                    validation_batch_size = std::max<std::size_t>(1, batch.size() / 2);
                }
                continue;
            }

            validation_batch_size = options.validation_batch_size;
            for (std::size_t candidate_idx : batch)
            {
                const auto &[x, y] = collector.candidates()[candidate_idx];
                auto xi = views_by_bv.find((Z3_ast)x);
                auto yi = views_by_bv.find((Z3_ast)y);
                if (xi == views_by_bv.end() || yi == views_by_bv.end())
                    continue;

                for (std::size_t lhs_idx : xi->second)
                {
                    for (std::size_t rhs_idx : yi->second)
                    {
                        const BvInfo &lhs = ring_bv[lhs_idx];
                        const BvInfo &rhs = ring_bv[rhs_idx];
                        if (lhs.bv_width != rhs.bv_width || lhs.conv_func != rhs.conv_func)
                            continue;
                        if (record_proved(lhs.conv_func,
                                          lhs.bv_term.decl().name().str(),
                                          rhs.bv_term.decl().name().str(),
                                          "callback-proved"))
                            ++discovered;
                    }
                }
            }
        }

        LOG_INFO(log, "bveq",
                 "[bv-eq-prover] callback total: " + std::to_string(discovered) +
                     " equality(ies), " + std::to_string(checks) +
                     " validation check(s); candidate-search=" +
                     util::fmt_duration(candidate_search_t1 - candidate_search_t0) +
                     "; validation=" +
                     util::fmt_duration(clk::now() - validation_t0));
        if (discovered != 0)
            return result;
    }

    if (!options.enable_fallback)
    {
        LOG_INFO(log, "bveq", "[bv-eq-prover] callback candidates insufficient; model fallback disabled");
        return result;
    }

    LOG_INFO(log, "bveq", "[bv-eq-prover] callback candidates insufficient; using model fallback");

    std::map<std::pair<unsigned, std::string>, std::vector<size_t>> groups;
    for (size_t i = 0; i < ring_bv.size(); ++i)
        groups[{ring_bv[i].bv_width, ring_bv[i].conv_func}].push_back(i);

    size_t total_discovered = 0;
    size_t total_checks = 0;
    const size_t MAX_CHECKS = 50000;

    auto partition_by_model = [&](const model &mdl, const std::vector<size_t> &group)
    {
        std::map<std::string, std::vector<size_t>> sub;
        for (size_t idx : group)
        {
            expr val = mdl.eval(ring_bv[idx].bv_term, true);
            sub[val.to_string()].push_back(idx);
        }
        return sub;
    };

    for (const auto &[key, indices] : groups)
    {
        if (indices.size() < 2)
            continue;

        LOG_INFO(log, "bveq",
                 "[bv-eq-prover] group (width=" + std::to_string(key.first) +
                     ", conv=" + key.second + "): " +
                     std::to_string(indices.size()) + " variable(s)");

        solver base_solver(ctx);
        base_solver.set("timeout", 30000u);
        for (const expr &c : bv_constraints)
            base_solver.add(c);

        check_result r = base_solver.check();
        if (r != sat)
        {
            LOG_INFO(log, "bveq",
                     "[bv-eq-prover] group solver returned " +
                         std::string(r == unsat ? "unsat" : "unknown") + "; skipping");
            continue;
        }
        model mdl = base_solver.get_model();

        auto initial_partition = partition_by_model(mdl, indices);

        size_t multi_groups = 0;
        size_t max_group_size = 0;
        for (const auto &[val, cands] : initial_partition)
        {
            if (cands.size() >= 2)
            {
                ++multi_groups;
                if (cands.size() > max_group_size)
                    max_group_size = cands.size();
            }
        }
        LOG_INFO(log, "bveq",
                 "[bv-eq-prover] initial partition: " +
                     std::to_string(initial_partition.size()) + " class(es), " +
                     std::to_string(multi_groups) + " with >=2, " +
                     "max=" + std::to_string(max_group_size));

        std::vector<std::vector<size_t>> work_queue;
        for (auto &[val, cands] : initial_partition)
            if (cands.size() >= 2)
                work_queue.push_back(std::move(cands));

        while (!work_queue.empty() && total_checks < MAX_CHECKS)
        {
            std::vector<size_t> group = std::move(work_queue.back());
            work_queue.pop_back();
            if (group.size() < 2)
                continue;

            size_t rep = group[0];
            std::vector<size_t> equal_to_rep = {rep};
            std::vector<size_t> to_check(group.begin() + 1, group.end());

            while (!to_check.empty() && total_checks < MAX_CHECKS)
            {
                size_t x = to_check.back();
                to_check.pop_back();
                ++total_checks;

                solver eq_check(ctx);
                eq_check.set("timeout", 10000u);
                for (const expr &c : bv_constraints)
                    eq_check.add(c);
                eq_check.add(ring_bv[rep].bv_term != ring_bv[x].bv_term);

                check_result eq_r = eq_check.check();
                if (eq_r == unsat)
                {
                    equal_to_rep.push_back(x);
                }
                else if (eq_r == sat)
                {
                    model cex = eq_check.get_model();

                    expr rep_val = cex.eval(ring_bv[rep].bv_term, true);
                    std::string rep_vs = rep_val.to_string();

                    std::vector<size_t> still_with_rep;
                    std::map<std::string, std::vector<size_t>> split;

                    for (size_t y : to_check)
                    {
                        expr yv = cex.eval(ring_bv[y].bv_term, true);
                        std::string yvs = yv.to_string();
                        if (yvs == rep_vs)
                            still_with_rep.push_back(y);
                        else
                            split[yvs].push_back(y);
                    }

                    expr xv = cex.eval(ring_bv[x].bv_term, true);
                    std::string xvs = xv.to_string();
                    split[xvs].push_back(x);

                    to_check = std::move(still_with_rep);

                    for (auto &[sv, sg] : split)
                        if (sg.size() >= 2)
                            work_queue.push_back(std::move(sg));
                }
            }

            const std::string &conv = ring_bv[rep].conv_func;
            std::string rep_name = ring_bv[rep].bv_term.decl().name().str();
            for (size_t i = 1; i < equal_to_rep.size(); ++i)
            {
                std::string b = ring_bv[equal_to_rep[i]].bv_term.decl().name().str();
                if (record_proved(conv, rep_name, b, "fallback-proved"))
                    ++total_discovered;
            }
        }
    }

    LOG_INFO(log, "bveq",
             "[bv-eq-prover] fallback total: " + std::to_string(total_discovered) +
                 " new equality(ies), " +
                 std::to_string(total_checks) + " solver call(s)");
    return result;
}

struct EqPInjectionDecls
{
    Z3_func_decl pconst = nullptr;
    Z3_func_decl eqp = nullptr;
};

static void collect_eqp_injection_decls_rec(const expr &e, EqPInjectionDecls &decls)
{
    if (!e.is_app())
        return;

    const std::string name = e.decl().name().str();
    if (name == "PConst" && e.num_args() == 1)
        decls.pconst = (Z3_func_decl)e.decl();
    else if (name == "eqP" && e.num_args() == 2)
        decls.eqp = (Z3_func_decl)e.decl();

    for (unsigned i = 0; i < e.num_args(); ++i)
        collect_eqp_injection_decls_rec(e.arg(i), decls);
}

static EqPInjectionDecls collect_eqp_injection_decls(const std::vector<expr> &asserts)
{
    EqPInjectionDecls decls;
    for (const expr &a : asserts)
        collect_eqp_injection_decls_rec(a, decls);
    return decls;
}

static expr mk_decl_app(context &ctx, Z3_func_decl raw, const std::vector<expr> &args)
{
    if (!raw)
        throw std::runtime_error("missing declaration for eqP injection");
    func_decl fd(ctx, raw);
    return fd((unsigned)args.size(), args.data());
}

static expr mk_injected_pconst(const EqPInjectionDecls &decls, const expr &v)
{
    return mk_decl_app(v.ctx(), decls.pconst, {v});
}

static expr mk_injected_eqp(const EqPInjectionDecls &decls, const expr &lhs, const expr &rhs)
{
    return mk_decl_app(lhs.ctx(), decls.eqp, {lhs, rhs});
}

std::vector<expr> inject_as_eqp(context &ctx,
                                const std::vector<expr> &asserts,
                                const Result &result,
                                util::Logger &log)
{
    std::vector<expr> injected;
    if (result.equalities.empty())
        return injected;

    EqPInjectionDecls decls = collect_eqp_injection_decls(asserts);
    if (!decls.pconst || !decls.eqp)
    {
        LOG_WARN(log, "eqgb",
                 "cannot inject proved BV equalities as eqP: missing PConst or eqP declaration in assertions");
        return injected;
    }

    std::unordered_set<Z3_ast> base_set;
    for (const expr &a : asserts)
        collect_coeff_bases_rec(a, base_set);

    std::unordered_map<std::string, Z3_ast> base_by_key;
    for (Z3_ast ast : base_set)
    {
        expr base(ctx, ast);
        if (!is_bv_to_int_app(base))
            continue;
        expr bv = base.arg(0);
        if (!bv.is_const() || bv.is_numeral())
            continue;
        const std::string key = base.decl().name().str() + ":" + bv.decl().name().str();
        base_by_key.emplace(key, ast);
    }

    std::unordered_set<std::string> seen;
    std::size_t skipped = 0;
    for (const ProvedEquality &proved : result.equalities)
    {
        auto lhs_it = base_by_key.find(proved.conversion + ":" + proved.lhs_bv);
        auto rhs_it = base_by_key.find(proved.conversion + ":" + proved.rhs_bv);
        if (lhs_it == base_by_key.end() || rhs_it == base_by_key.end())
        {
            ++skipped;
            continue;
        }

        expr lhs_base(ctx, lhs_it->second);
        expr rhs_base(ctx, rhs_it->second);
        expr lhs_poly = mk_injected_pconst(decls, lhs_base);
        expr rhs_poly = mk_injected_pconst(decls, rhs_base);
        expr eqp = mk_injected_eqp(decls, lhs_poly, rhs_poly);
        if (seen.insert(eqp.to_string()).second)
            injected.push_back(eqp);
    }

    LOG_INFO(log, "eqgb",
             "injected " + std::to_string(injected.size()) +
                 " proved BV equality eqP assertion(s) for Z3 rewrite" +
                 (skipped == 0 ? "" : "; skipped=" + std::to_string(skipped)));
    return injected;
}

// ---------------- Indet environment ----------------

} // namespace util::bveq
