use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub struct MemRegion {
    pub base: nat,
    pub size: nat,
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


// File: spec_t/hlspec.rs
#[allow(inconsistent_fields)]
pub enum ThreadState {
    Map { vaddr: nat, pte: PTE },
    Unmap { vaddr: nat, pte: Option<PTE> },
    Idle,
}

pub open spec fn if_map_then_unique(thread_state: Map<nat, ThreadState>, id: nat) -> bool
    recommends thread_state.contains_key(id),
{
    thread_state[id] matches ThreadState::Map { vaddr, pte }
        ==> !thread_state.remove(id).values().contains(thread_state[id])
}

pub open spec fn inflight_maps_unique(thread_state: Map<nat, ThreadState>) -> bool {
    forall|a: nat| #[trigger] thread_state.contains_key(a) ==> if_map_then_unique(thread_state, a)
}


// File: spec_t/hlproof.rs
pub proof fn insert_non_map_preserves_unique(
    thread_state: Map<nat, ThreadState>,
    base: nat,
    arg: ThreadState,
)
    requires
        inflight_maps_unique(thread_state),
        !(arg is Map),
    ensures
        inflight_maps_unique(thread_state.insert(base, arg)),
{

}


}
