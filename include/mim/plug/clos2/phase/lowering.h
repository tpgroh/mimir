#pragma once

#include "mim/phase.h"

#include "mim/plug/clos2/autogen.h"
#include "mim/plug/clos2/fv.h"
#include "mim/plug/mem/mem.h"

namespace mim::plug::clos2 {

// TODO: Drop the rewrites to `clos.*` as soon as clos2 is an in-tree plugin and `ll` lowers clos2's setjmp/longjmp annexes itself.
// TODO: Make the environment parameter of every procedure a void pointer as well.
//       At the procedure's entry, cast that void pointer to a pointer to the procedure's environment type and load the environment through it.
// TODO: Allocate every environment at its creation site, so that a closure holds a pointer to its environment.
//       Until then, the closure casts the environment tuple itself to the void pointer.
//       This might require absclos_elim to keep annotating the creation sites, as this phase has to find them after the FCC optimizations that run between absclos_elim and this phase.

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

    const Def* rewrite_imm_Tuple(const Tuple* tuple) final {
        if (auto [proc, env] = isa_packing(tuple); proc) return rewrite_packing(proc, env);
        return RWPhase::rewrite_imm_Tuple(tuple);
    }

    const Def* void_ptr() { return new_world().call<mem::Ptr0>(new_world().type_i8()); }

private:
    DefSet procedures_{};
    const Def* curr_mem_ = nullptr;
    Def2Def self_ptrs_{};
    FVAnalysis fvana_{};
};

} // namespace mim::plug::clos2
