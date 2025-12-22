use vstd::prelude::*;
use crate::defs::*;

fn main() {}

verus!{

global size_of usize == 8;

pub mod defs {
    use vstd::prelude::*;

// File: spec_t/mmu/defs.rs
#[derive(Copy, Clone)]
pub struct Core {
    pub node_id: nat,
    pub core_id: nat,
}

pub struct MemRegion {
    pub base: nat,
    pub size: nat,
}

pub open spec fn overlap(region1: MemRegion, region2: MemRegion) -> bool {
    if region1.base <= region2.base {
        region1.base == region2.base || region2.base < region1.base + region1.size
    } else {
        region1.base < region2.base + region2.size
    }
}

#[derive(Copy, Clone)]
pub struct Flags {
    pub is_writable: bool,
    pub is_supervisor: bool,
    pub disable_execute: bool,
}

pub struct PTE {
    pub frame: MemRegion,
    /// The `flags` field on a `PTE` denotes the combined flags of the entire
    /// translation path to the entry. (See page table walk definition in hardware model,
    /// `spec_t::hardware`.) However, because we always set the flags on directories to be
    /// permissive these flags also correspond to the flags that we set for the frame mapping
    /// corresponding to this `PTE`.
    pub flags: Flags,
}
}

pub mod os {
    use vstd::prelude::*;
    use crate::defs::*;

// File: spec_t/os.rs
pub struct Constants {
    /// Constants for mmu and os_ext state machines
    pub common: crate::Constants,
    //maps User Level Thread to its assigned core
    pub ult2core: Map<nat, Core>,
    //highest thread_id
    pub ult_no: nat,
}

#[allow(inconsistent_fields)]
pub enum CoreState {
    Idle,
    MapWaiting { ult_id: nat, vaddr: nat, pte: PTE },
    MapExecuting { ult_id: nat, vaddr: nat, pte: PTE },
    MapDone { ult_id: nat, vaddr: nat, pte: PTE, result: Result<(), ()> },
    UnmapWaiting { ult_id: nat, vaddr: nat },
    UnmapExecuting { ult_id: nat, vaddr: nat, result: Option<Result<PTE, ()>> },
    UnmapOpDone { ult_id: nat, vaddr: nat, result: Result<PTE, ()> },
    UnmapShootdownWaiting { ult_id: nat, vaddr: nat, result: Result<PTE, ()> },
}

impl CoreState {

    #[verifier(inline)]
    pub open spec fn is_idle(self) -> bool {
        self is Idle
    }

}


pub open spec fn inflight_vmem_region(pt: Map<nat, PTE>, core_state: CoreState) -> MemRegion
    recommends !(core_state is Idle)
{
    match core_state {
        CoreState::Idle => arbitrary(),
        CoreState::MapWaiting { vaddr, pte, .. }
        | CoreState::MapExecuting { vaddr, pte, .. }
        | CoreState::MapDone { vaddr, pte, .. } => {
            MemRegion { base: vaddr, size: pte.frame.size }
        }

        CoreState::UnmapWaiting { vaddr, .. }
        | CoreState::UnmapExecuting { vaddr, result: None, .. } => {
            let size = if pt.contains_key(vaddr) { pt[vaddr].frame.size } else { 0 };
            MemRegion { base: vaddr, size: size }
        }

        CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: Some(result) }
        | CoreState::UnmapOpDone { ult_id: ult_id2, vaddr, result }
        | CoreState::UnmapShootdownWaiting { ult_id: ult_id2, vaddr, result } => {
            let size = if result is Ok { result.get_Ok_0().frame.size } else { 0 };
            MemRegion { base: vaddr, size: size }
        }
    }
}

pub open spec fn candidate_mapping_overlaps_inflight_vmem(
    pt: Map<nat, PTE>,
    inflightargs: Set<CoreState>,
    base: nat,
    candidate_size: nat,
) -> bool {
    exists|core_state: CoreState| #![auto] {
        &&& inflightargs.contains(core_state)
        &&& !(core_state is Idle)
        &&& overlap(
                inflight_vmem_region(pt, core_state),
                MemRegion { base: base, size: candidate_size },
            )
    }
}

impl CoreState {

    pub open spec fn pte_size(self, pt: Map<nat, PTE>) -> nat
        recommends !self.is_idle(),
    {
        match self {
            CoreState::MapWaiting { pte, .. }
            | CoreState::MapExecuting { pte, .. }
            | CoreState::MapDone { pte, .. } => {
                pte.frame.size
            },
            CoreState::UnmapWaiting { vaddr, .. }
            | CoreState::UnmapExecuting { vaddr, result: None, .. } => {
                if pt.contains_key(vaddr) { pt[vaddr].frame.size } else { 0 }
            },
            CoreState::UnmapExecuting { result: Some(result), .. }
            | CoreState::UnmapOpDone { result, .. }
            | CoreState::UnmapShootdownWaiting { result, .. } => {
                if result is Ok { result.get_Ok_0().frame.size } else { 0 }
            },
            CoreState::Idle => arbitrary(),
        }
    }

    pub open spec fn vaddr(self) -> nat
        recommends !self.is_idle(),
    {
        match self {
            CoreState::MapWaiting { vaddr, .. }
            | CoreState::MapExecuting { vaddr, .. }
            | CoreState::MapDone { vaddr, .. }
            | CoreState::UnmapWaiting { vaddr, .. }
            | CoreState::UnmapExecuting { vaddr, .. }
            | CoreState::UnmapOpDone { vaddr, .. }
            | CoreState::UnmapShootdownWaiting { vaddr, .. } => { vaddr },
            CoreState::Idle => arbitrary(),
        }
    }

}
}

// File: spec_t/mmu/mod.rs
pub struct Constants {
    pub node_count: nat,
    pub core_count: nat,
    /// The range of memory used for the page table
    pub range_ptmem: (nat, nat),
    /// The range of memory used for the user memory
    pub range_mem: (nat, nat),
    pub phys_mem_size: nat,
}


// File: spec_t/os_invariant.rs
pub open spec fn unique_CoreStates(map: Map<Core, os::CoreState>) -> bool {
    forall|core| #![auto] map.contains_key(core) && !map[core].is_idle()
        ==> !map.remove(core).values().contains(map[core])
}

pub open spec fn no_overlap_vmem_values(
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
) -> bool {
    forall|state1: os::CoreState, state2: os::CoreState|
        core_states.values().contains(state1) && core_states.values().contains(state2)
            && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.pte_size(pt) },
        ) ==> state1 == state2
}

pub proof fn lemma_insert_no_overlap_preserves_no_overlap(
    c: os::Constants,
    core_states: Map<Core, os::CoreState>,
    pt: Map<nat, PTE>,
    core: Core,
    corestate: os::CoreState,
)
    requires
        core_states.dom().contains(core),
        unique_CoreStates(core_states),
        no_overlap_vmem_values(core_states, pt),
        core_states[core].is_idle(),
        !corestate.is_idle(),
        !os::candidate_mapping_overlaps_inflight_vmem(
            pt,
            core_states.values(),
            corestate.vaddr(),
            corestate.pte_size(pt),
        ),
    ensures
        unique_CoreStates(core_states.insert(core, corestate)),
        no_overlap_vmem_values(core_states.insert(core, corestate), pt),
{
    assert forall|a| #![auto]
        core_states.insert(core, corestate).dom().contains(a)
        && !core_states.insert(core, corestate)[a].is_idle()
        implies !core_states.insert(core, corestate).remove(a).values()
                            .contains(core_states.insert(core, corestate)[a])
    by {
        if core_states.insert(core, corestate).remove(a).values().contains(
            core_states.insert(core, corestate)[a],
        ) {
            let some_core = choose|cr|
                #![auto]
                cr != a && core_states.insert(core, corestate).dom().contains(cr)
                    && core_states.insert(core, corestate)[cr] == core_states.insert(
                    core,
                    corestate,
                )[a];
            if a == core || some_core == core {
                let other = if some_core != core { some_core } else { a };
                assert(core_states.values().contains(core_states[other]));
                assert(overlap(
                    MemRegion {
                        base: core_states[other].vaddr(),
                        size: core_states[other].pte_size(pt),
                    },
                    MemRegion { base: corestate.vaddr(), size: corestate.pte_size(pt) },
                ));
            } else {
                assert(core_states.remove(a).dom().contains(some_core));
            }
        }
    }
    assert forall|state1: os::CoreState, state2: os::CoreState|
        core_states.insert(core, corestate).values().contains(state1) && core_states.insert(
            core,
            corestate,
        ).values().contains(state2) && !state1.is_idle() && !state2.is_idle() && overlap(
            MemRegion { base: state1.vaddr(), size: state1.pte_size(pt) },
            MemRegion { base: state2.vaddr(), size: state2.pte_size(pt) },
        ) implies state1 == state2 by {
        if state1 == corestate || state2 == corestate {
            let other = if state1 != corestate {
                state1
            } else {
                state2
            };
            if other != corestate {
                assert(core_states.values().contains(other));
                assert(overlap(
                    MemRegion { base: other.vaddr(), size: other.pte_size(pt) },
                    MemRegion { base: corestate.vaddr(), size: corestate.pte_size(pt) },
                ));
                assert(false);
            }
        }
    }
}


}
