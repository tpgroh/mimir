#include "mim/plug/clos2/phase/lowering.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

const Def* Lowering::rewrite_procedure(Lam* old_proc) {
    auto& w = new_world();
    auto [old_clos, old_arg] = old_proc->vars<2>();

    // create new type for the procedure, lambda lifting free variables in the type
    // note that this means dependencies on the environment.
    // the equality problem for those with the packaged value in the environment will be solved
    // by the typecast of the closure pointer.
    auto fvset = fvana_.free_vars(old_arg->type());
    auto fvs = DefVec{fvset.begin(), fvset.end()};
    // TODO: lambda lifting needs a syntax-driven order that the call sites can reproduce; GID order is a placeholder.
    std::ranges::sort(fvs, GIDLt<const Def*>());

    // assert(old_arg->type()->free_vars().size() == 1 && "the free variables can only be the environment var of old_proc");
    // assert(old_arg->type()->free_vars().contains(old_clos) && "the free variables can only be the environment var of old_proc");

    // create the domain of the new procedure
    auto r = old_arg->num_projs();
    auto k = fvs.size();
    auto n = k + r + 1; // lifted free vars, closure pointer, arguments
    auto new_dom = w.mut_sigma(w.type_pending(), n);

    push();
    bind_old(old_proc->has_var());
    bind_new(new_dom->var()->isa<Var>());
    for (size_t i = 0; i < k; i++) {
        new_dom->set(i, rewrite(fvs[i]->type()));
        map(fvs[i], new_dom->var(n, i));
    }
    new_dom->set(k, void_ptr());
    for (size_t j = 0; j < r; j++) {
        new_dom->set(k + j +1, rewrite(old_arg->proj(r, j)->type()));
        map(old_arg->proj(r, j), new_dom->var(n, k + j +1));
    }
    pop();

    log().d("new domain {}", new_dom);

    // create new procedure
    auto new_proc = w.mut_con(new_dom);
    new_proc->set(old_proc->dbg_key());
    map(old_proc, new_proc); // we want this mapping to percist

    push();
    bind_old(old_proc->has_var());
    bind_new(new_proc->var()->isa<Var>());

    auto old_env = old_clos->proj(2, 1);
    auto p = old_env->num_projs();
    // use lambda lifted values instead of those from the environment
    for (size_t i = 0; i < k; i++) map(fvs[i], new_proc->var(n, i));
    auto env_t = w.sigma(DefVec{p, [&](auto i){ return rewrite(old_env->proj(p, i)->type()); }});
    auto rec_t = w.sigma({new_proc->type(), env_t});
    auto rec_ptr = w.call<core::bitcast>(w.call<mem::Ptr0>(rec_t), new_proc->var(n, k));

    log().d("rec_ptr {} of type {}", rec_ptr, rec_ptr->type());

    // now load the environment.
    // note that this is not dead code if the loaded values are not used, because we use the returned memory thing.
    // this load could be skiped if the environment is not used inside the body.
    assert(Axm::isa<mem::M>(old_arg->proj(r, 0)->type()) && "the first argument to a procedure should have been mem::M");
    auto [m, rec] = w.call<mem::load>(Defs{new_proc->var(n, k+1), rec_ptr})->projs<2>();

    self_ptrs_[old_clos] = new_proc->var(n, k); // for self recursion
    map(old_clos, rec); // use the loaded environment
    map(old_arg, w.tuple(DefVec{r, [&](size_t j){ return j == 0 ? m : new_proc->var(n, k + j +1); }}));

    new_proc->set(rewrite(old_proc->filter()), rewrite(old_proc->body()));
    pop();

    return new_proc;
}

const Def* Lowering::rewrite_packing(const Def* old_proc, const Def* old_env) {
    auto& w = new_world();

    // recursive call: pass the incoming closure on instead of allocating again
    if (auto ex = old_proc->isa<Extract>()) return self_ptrs_.at(ex->tuple());

    if (!curr_mem_) old_proc->blame("closure created in a continuation without memory").bail();

    auto proc     = rewrite(old_proc);
    auto rec      = w.tuple({proc, rewrite(old_env)});
    auto [m, ptr] = mem::op_alloc(rec->type(), curr_mem_)->projs<2>();
    curr_mem_     = w.call<mem::store>(Defs{m, ptr, rec});
    return w.call<core::bitcast>(void_ptr(), ptr);
}
