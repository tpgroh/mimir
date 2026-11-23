#pragma once

#include "mim/phase.h"

#include "mim/plug/clos2/phase/absclos_elim.h"
#include "mim/plug/clos2/fv.h"
#include "mim/plug/mem/mem.h"

namespace mim::plug::clos2 {

/// Lowers what is left of clos2 for the ll backend; runs last.
class Lowering : public RWPhase {
public:
    Lowering(World& world, flags_t annex)
        : RWPhase(world, annex) {}

private:
    void analyze_visit(const Def* def, DefSet& done) {
        if (!done.insert(def).second) return;

        // detect procedures.
        // every unsafe_cast that is not to clos2::Env is a procedure
        if (auto cast = Axm::isa<clos2::unsafe_cast>(def))
            if (auto lam = cast->arg()->isa_mut<Lam>(); lam && cast->type() != old_world().annex<clos2::Env>())
                procedures_.emplace(lam);

        for (auto d : def->deps()) analyze_visit(d, done);
    }

    bool analyze() final {
        DefSet done;

        for (auto mut : old_world().externals().muts())
            analyze_visit(mut, done);

        return false;
    }

    const Def* rewrite_procedure(Lam*);
    const Def* rewrite_mut_Lam(Lam* old_lam) final {
        if (procedures_.contains(old_lam)) return rewrite_procedure(old_lam);

        // we require mem::M for closure packing.
        // the creation will be placed at the start of the lambda in which the creation happens.

        auto old_m = mem::mem_var(old_lam);
        if (!old_m) {
            log().d("did not find mem in {}", old_lam->type());
            auto _ = fe::Restore(curr_mem_, {});
            return RWPhase::rewrite_mut_Lam(old_lam);
        }

        auto& w      = new_world();
        auto new_lam = w.mut_lam(rewrite(old_lam->type())->as<Pi>());
        map(old_lam, new_lam);

        push();
        bind_old(old_lam->has_var());
        bind_new(new_lam->var()->isa<Var>());

        auto rest = mem::mut_con(w); // the old body, entered with the memory after all closure creations
        map(old_m, rest->var());

        auto _  = fe::Restore(curr_mem_, mem::mem_var(new_lam));
        auto __ = enter(old_lam); // TODO: replace with _ when switching to c++26
        rest->set(true, rewrite(old_lam->body()));
        new_lam->set(rewrite(old_lam->filter()), w.app(rest, curr_mem_));
        pop();
        return new_lam;
    }

    const Def* rewrite_packing(const Def*, const Def*);

    std::pair<const Def*, const Def*> isa_packing(const Tuple* tuple) {
        if (tuple->num_ops() != 2) return {};
        auto code = Axm::isa<clos2::unsafe_cast>(tuple->op(0));
        auto env  = Axm::isa<clos2::unsafe_cast>(tuple->op(1));
        if (code && env && env->type() == old_world().annex<clos2::Env>()) return {code->arg(), env->arg()};
        return {};
    }


    const Def* rewrite_mut_Sigma(Sigma* sigma) final {
        if (!Closure::isa_closure_type(sigma)) return RWPhase::rewrite_mut_Sigma(sigma);
        auto& w    = new_world();
        auto arg_t = Pi::isa_cn(sigma->op(0))->dom(2, 1);
        return map(sigma, w.sigma({w.cn(lifted_dom(sorted_fvs(arg_t), arg_t)), void_ptr()}));
    }

    const Def* rewrite_imm_Tuple(const Tuple* tuple) final {
        if (auto [proc, env] = isa_packing(tuple); proc) return rewrite_packing(proc, env);
        return RWPhase::rewrite_imm_Tuple(tuple);
    }



    const Def* rewrite_clos_call(const Def*, const Def*);
    const Def* rewrite_imm_App(const App* app) final {
        if (auto [c, a] = isa_clos_call(app); c) return rewrite_clos_call(c, a);
        return RWPhase::rewrite_imm_App(app);
    }

    std::pair<const Def*, const Def*> isa_clos_call(const App* app) {
        if (app->num_args() != 2) return {};
        auto [c, a] = app->args<2>();
        if (Closure::isa_closure_type(c->type())) return {c, a};
        return {};
    }

    const Def* void_ptr() { return new_world().call<mem::Ptr0>(new_world().type_i8()); }


    DefVec sorted_fvs(const Def* type) {
        auto fvset = fvana_.free_vars(type);
        auto fvs   = DefVec{fvset.begin(), fvset.end()};
        // TODO: syntax-driven order; procedure and closure type only agree on GID order for at most one lifted var.
        std::ranges::sort(fvs, GIDLt<const Def*>());
        return fvs;
    }


    /// [l₀, …, lₖ₋₁, env, a₀, …, aᵣ₋₁] with the fvs and arg_t's own var abstracted.
    Sigma* lifted_dom(const DefVec& fvs, const Def* arg_t) {
        auto& w  = new_world();
        auto k   = fvs.size();
        auto r   = arg_t->num_projs();
        auto n   = k + 1 + r;
        auto dom = w.mut_sigma(w.type_pending(), n);

        push();
        bind_old(arg_t->has_var());
        bind_new(dom->var()->isa<Var>());
        for (size_t i = 0; i < k; ++i) {
            dom->set(i, rewrite(fvs[i]->type()));
            map(fvs[i], dom->var(n, i));
        }
        dom->set(k, void_ptr());
        for (size_t j = 0; j < r; ++j) {
            dom->set(k + 1 + j, rewrite(arg_t->proj(r, j)));
            if (auto v = arg_t->has_var()) map(v->proj(r, j), dom->var(n, k + 1 + j));
        }
        pop();
        return dom;
    }

private:
    DefSet procedures_{};
    const Def* curr_mem_ = nullptr;
    Def2Def self_clos_{};
    FVAnalysis fvana_{};
};

} // namespace mim::plug::clos2
