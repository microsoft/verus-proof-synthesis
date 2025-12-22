use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec fn candidate_mapping_overlaps_existing_vmem(
    mappings: Map<nat, PTE>,
    base: nat,
    pte: PTE,
) -> bool {
    exists|b: nat| {
        &&& #[trigger] mappings.contains_key(b)
        &&& overlap(
            MemRegion { base: base, size: pte.frame.size },
            MemRegion { base: b, size: mappings[b].frame.size },
        )
    }
}

pub open spec fn candidate_mapping_overlaps_existing_pmem(mappings: Map<nat, PTE>, pte: PTE) -> bool {
    exists|b: nat| #![auto] {
            &&& mappings.dom().contains(b)
            &&& overlap(pte.frame, mappings.index(b).frame)
        }
}

#[derive(Copy, Clone)]
pub struct Core {
    pub node_id: nat,
    pub core_id: nat,
}

pub enum LoadResult {
    Pagefault,
    Value(Seq<u8>),
}

pub enum StoreResult {
    Pagefault,
    Ok,
}

#[allow(inconsistent_fields)]
pub enum MemOp {
    Load { is_exec: bool, size: nat, result: LoadResult },
    Store { new_value: Seq<u8>, result: StoreResult },
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


// File: spec_t/hlspec.rs
pub struct Constants {
    pub thread_no: nat,
    pub phys_mem_size: nat,
}

pub struct State {
    /// Byte-indexed virtual memory
    pub mem: Seq<u8>,
    pub thread_state: Map<nat, ThreadState>,
    /// `mappings` constrains the domain of mem and tracks the flags. We could instead move the
    /// flags into `map` as well and write the specification exclusively in terms of `map` but that
    /// also makes some of the enabling conditions awkward, e.g. full mappings have the same flags, etc.
    pub mappings: Map<nat, PTE>,
    pub sound: bool,
}

#[allow(inconsistent_fields)]
pub enum ThreadState {
    Map { vaddr: nat, pte: PTE },
    Unmap { vaddr: nat, pte: Option<PTE> },
    Idle,
}

pub open spec fn wf(c: Constants, s: State) -> bool {
    &&& forall|id: nat| id < c.thread_no <==> s.thread_state.contains_key(id)
    &&& s.mappings.dom().finite()
}

impl Constants {

    pub open spec fn valid_thread(self, thread_id: nat) -> bool {
        thread_id < self.thread_no
    }

}


pub open spec fn candidate_mapping_overlaps_inflight_pmem(
    inflightargs: Set<ThreadState>,
    candidate: PTE,
) -> bool {
    exists|b: ThreadState| #![auto] {
        &&& inflightargs.contains(b)
        &&& match b {
            ThreadState::Map { vaddr, pte } => overlap(candidate.frame, pte.frame),
            ThreadState::Unmap { vaddr, pte } => {
                &&& pte.is_some()
                &&& overlap(candidate.frame, pte.unwrap().frame)
            },
            _ => { false },
        }
    }
}

pub open spec fn step_MapEnd(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MapEnd { thread_id, vaddr, result }
    &&& s2.sound == s1.sound
    &&& c.valid_thread(thread_id)
    &&& s2.thread_state === s1.thread_state.insert(thread_id, ThreadState::Idle)
    &&& s1.thread_state[thread_id] matches ThreadState::Map { vaddr: vaddr2, pte }
    &&& vaddr == vaddr2
    &&& if candidate_mapping_overlaps_existing_vmem(s1.mappings, vaddr, pte) {
        &&& result is Err
        &&& s2.mappings === s1.mappings
    } else {
        &&& result is Ok
        &&& s2.mappings === s1.mappings.insert(vaddr, pte)
    }
    &&& s2.mem === s1.mem
}

pub open spec fn pmem_no_overlap(mappings: Map<nat, PTE>) -> bool {
    forall|bs1: nat, bs2: nat|
        mappings.contains_key(bs1) && mappings.contains_key(bs2)
        && overlap(mappings.index(bs1).frame, mappings.index(bs2).frame)
        ==> bs1 == bs2
}

pub open spec fn inflight_map_no_overlap_pmem(
    inflightargs: Set<ThreadState>,
    mappings: Map<nat, PTE>,
) -> bool {
    forall|b: ThreadState| #![auto]
        inflightargs.contains(b) && b is Map
            ==> !candidate_mapping_overlaps_existing_pmem(mappings, b->Map_pte)

}

pub open spec fn inflight_map_no_overlap_inflight_pmem(inflightargs: Set<ThreadState>) -> bool {
    forall|b: ThreadState| #![auto]
        inflightargs.contains(b) && b is Map
            ==> !candidate_mapping_overlaps_inflight_pmem(inflightargs.remove(b), b->Map_pte)
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

pub open spec fn inv(c: Constants, s: State) -> bool {
    &&& wf(c, s)
    &&& pmem_no_overlap(s.mappings)
    // invariants needed to prove the former
    &&& inflight_map_no_overlap_pmem(s.thread_state.values(), s.mappings)
    &&& inflight_map_no_overlap_inflight_pmem(s.thread_state.values())
    &&& inflight_maps_unique(s.thread_state)
}


// File: theorem.rs
pub enum RLbl {
    Tau,
    MemOp      { thread_id: nat, vaddr: nat, op: MemOp },
    MapStart   { thread_id: nat, vaddr: nat, pte: PTE },
    MapEnd     { thread_id: nat, vaddr: nat, result: Result<(), ()> },
    UnmapStart { thread_id: nat, vaddr: nat },
    UnmapEnd   { thread_id: nat, vaddr: nat, result: Result<(), ()> },
    AckShootdownIPI { core: Core },
}


// File: spec_t/hlproof.rs
	#[verifier::external_body]
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
		unimplemented!()
	}

pub proof fn map_end_preserves_inv(c: Constants, s1: State, s2: State, lbl: RLbl)
    requires
        step_MapEnd(c, s1, s2, lbl),
        s1.sound ==> inv(c, s1),
        s1.sound,
        s1.thread_state.contains_key(lbl->MapEnd_thread_id),
    ensures
        s2.sound ==> inv(c, s2),
{

}


}
