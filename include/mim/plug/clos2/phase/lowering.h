#pragma once

#include "mim/phase.h"

#include "mim/plug/clos/autogen.h"
#include "mim/plug/clos2/autogen.h"
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
    const Def* lookup(const Def* old_def) final {
        if (auto flags = old_world().annexes().flags(old_def))
            if (auto new_def = replacement(*flags)) return map(old_def, new_def);
        return RWPhase::lookup(old_def);
    }

    const Def* replacement(flags_t flags) {
        auto& w = new_world();
        if (flags == Annex::base<clos2::Env>()) return w.call<mem::Ptr0>(w.type_i8());
        if (flags == Annex::base<clos2::JmpBuf>()) return w.type_i8();
        if (flags == Annex::base<clos2::JmpBufPtr>()) return w.annex<clos::BufPtr>();
        if (flags == Annex::base<clos2::alloc_jmpbuf>()) return w.annex<clos::alloc_jmpbuf>();
        if (flags == Annex::base<clos2::setjmp>()) return w.annex<clos::setjmp>();
        if (flags == Annex::base<clos2::longjmp>()) return w.annex<clos::longjmp>();
        return nullptr;
    }
};

} // namespace mim::plug::clos2
