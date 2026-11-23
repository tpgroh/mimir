#include "mim/plug/clos2/phase/lowering.h"

using namespace mim;
using namespace mim::plug;
using namespace mim::plug::clos2;

const Def* Lowering::rewrite_procedure(Lam* old_proc) {
    auto& w = new_world();
    auto [old_clos, old_arg] = old_proc->vars<2>();

    auto fvs = sorted_fvs(old_arg->type());
    auto r = old_arg->num_projs();
    auto k = fvs.size();
    auto n = k + r + 1; // lifted free vars, closure pointer, arguments
    
    // create new procedure
    auto new_proc = w.mut_con(lifted_dom(fvs, old_arg->type()));
    new_proc->set(old_proc->dbg_key());
    map(old_proc, new_proc); // we want this mapping to percist

    push();
    bind_old(old_proc->has_var());
    bind_new(new_proc->var()->isa<Var>());
    for (size_t i = 0; i < k; i++)
        map(fvs[i], new_proc->var(n, i));

    auto ptr = new_proc->var(n, k);
    auto old_env = old_clos->proj(2, 1);
    auto e = old_env->num_projs();
    // use lambda lifted values instead of those from the environment
    auto env_t = w.sigma(DefVec{e, [&](auto i){ return rewrite(old_env->proj(e, i)->type()); }});
    auto env_ptr = w.call<core::bitcast>(w.call<mem::Ptr0>(env_t), ptr);

    // now load the environment.
    // note that this is not dead code if the loaded values are not used, because we use the returned memory thing.
    // this load could be skiped if the environment is not used inside the body.
    assert(Axm::isa<mem::M>(old_arg->proj(r, 0)->type()) && "the first argument to a procedure should have been mem::M");
    auto [m, env] = w.call<mem::load>(Defs{new_proc->var(n, k+1), env_ptr})->projs<2>();

    self_clos_[old_clos] = new_proc->var(n, k); // for self recursion
    map(old_clos, w.tuple({new_proc, env}));
    map(old_arg, w.tuple(DefVec{r, [&](size_t j){ return j == 0 ? m : new_proc->var(n, k + j +1); }}));

    new_proc->set(rewrite(old_proc->filter()), rewrite(old_proc->body()));
    pop();

    return new_proc;
}

const Def* Lowering::rewrite_packing(const Def* old_proc, const Def* old_env) {
    auto& w = new_world();

    // recursive call: pass the incoming closure on instead of allocating again
    if (auto ex = old_proc->isa<Extract>()) {
        auto clos = ex->tuple();
        auto it = self_clos_.find(clos);
        if (it == self_clos_.end() || old_env != clos->proj(2, 1))
            old_proc->blame("unexpected shape of a closure repack").bail();
        return it->second;
    }

    if (!curr_mem_) old_proc->blame("closure created in a continuation without memory").bail();

    auto proc     = rewrite(old_proc);
    auto env      = rewrite(old_env);
    auto [m, ptr] = mem::op_alloc(env->type(), curr_mem_)->projs<2>();
    curr_mem_     = w.call<mem::store>(Defs{m, ptr, env});
    return w.tuple({proc, w.call<core::bitcast>(void_ptr(), ptr)});
}

const Def* Lowering::rewrite_clos_call(const Def* old_c, const Def* old_a) {
    auto& w          = new_world();
    auto fvs         = sorted_fvs(old_a->type());
    auto r           = old_a->num_projs();
    auto [code, env] = rewrite(old_c)->projs<2>();

    auto args = DefVec{};
    for (auto f : fvs) args.emplace_back(rewrite(f));
    args.emplace_back(env);
    for (size_t j = 0; j < r; ++j) args.emplace_back(rewrite(old_a->proj(r, j)));
    return w.app(code, args);
}
