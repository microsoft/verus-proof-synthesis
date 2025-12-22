use vstd::prelude::*;

fn main() {}

verus!{

global size_of usize == 8;

// File: spec_t/mmu/defs.rs
pub const X86_NUM_LAYERS: usize = 4;

pub const X86_NUM_ENTRIES: usize = 512;

#[verifier(external_body)]
pub const MAX_PHYADDR_WIDTH: usize = 52;

pub axiom fn axiom_max_phyaddr_width_facts()
    ensures
        32 <= MAX_PHYADDR_WIDTH <= 52,
;

// We cannot use a dual exec/spec constant for MAX_PHYADDR, because for those Verus currently
// doesn't support manually guiding the no-overflow proofs.
pub spec const MAX_PHYADDR_SPEC: usize = ((1usize << MAX_PHYADDR_WIDTH) - 1usize) as usize;

#[verifier::when_used_as_spec(MAX_PHYADDR_SPEC)]
pub exec const MAX_PHYADDR: usize ensures MAX_PHYADDR == MAX_PHYADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    assert(1usize << 32 == 0x100000000) by (compute);
    assert(forall|m:usize,n:usize|  n < m < 64 ==> 1usize << n < 1usize << m) by (bit_vector);
    (1usize << MAX_PHYADDR_WIDTH) - 1usize
}

pub const PAGE_SIZE: usize = 4096;

pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 512 * 512 * 4096;

pub const L3_ENTRY_SIZE: usize = PAGE_SIZE;

pub const L2_ENTRY_SIZE: usize = 512 * L3_ENTRY_SIZE;

pub const L1_ENTRY_SIZE: usize = 512 * L2_ENTRY_SIZE;

pub const L0_ENTRY_SIZE: usize = 512 * L1_ENTRY_SIZE;

pub open spec fn entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + idx * entry_size
}

pub open spec fn candidate_mapping_in_bounds(base: nat, pte: PTE) -> bool {
    base + pte.frame.size < x86_arch_spec.upper_vaddr(0, 0)
}

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

pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

pub open spec fn between(x: nat, a: nat, b: nat) -> bool {
    a <= x && x < b
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

impl MemOp {

    pub open spec fn is_pagefault(self) -> bool {
        ||| self matches MemOp::Load { result: LoadResult::Pagefault, .. }
        ||| self matches MemOp::Store { result: StoreResult::Pagefault, .. }
    }

    pub open spec fn op_size(self) -> nat {
        match self {
            MemOp::Load { size, .. } => size,
            MemOp::Store { new_value, .. } => new_value.len(),
        }
    }

    pub open spec fn valid_op_size(self) -> bool {
        ||| self.op_size() == 1
        ||| self.op_size() == 2
        ||| self.op_size() == 4
        ||| self.op_size() == 8
    }

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

pub ghost struct ArchLayer {
    /// Address space size mapped by a single entry at this layer
    pub entry_size: nat,
    /// Number of entries at this layer
    pub num_entries: nat,
}

pub ghost struct Arch {
    pub layers: Seq<ArchLayer>,
    // [512G, 1G  , 2M  , 4K  ]
    // [512 , 512 , 512 , 512 ]
}

impl Arch {

    pub open spec(checked) fn entry_size(self, layer: nat) -> nat
        recommends
            layer < self.layers.len(),
    {
        self.layers[layer as int].entry_size
    }

    pub open spec(checked) fn num_entries(self, layer: nat) -> nat
        recommends
            layer < self.layers.len(),
    {
        self.layers.index(layer as int).num_entries
    }

    pub open spec(checked) fn upper_vaddr(self, layer: nat, base: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        self.entry_base(layer, base, self.num_entries(layer))
    }

    pub open spec(checked) fn inv(&self) -> bool {
        &&& self.layers.len() <= X86_NUM_LAYERS
        &&& forall|i: nat|
            #![trigger self.entry_size(i)]
            #![trigger self.num_entries(i)]
            i < self.layers.len() ==> {
                &&& 0 < self.entry_size(i) <= X86_MAX_ENTRY_SIZE
                &&& 0 < self.num_entries(i) <= X86_NUM_ENTRIES
                &&& self.entry_size_is_next_layer_size(i)
            }
    }

    pub open spec(checked) fn entry_size_is_next_layer_size(self, i: nat) -> bool
        recommends
            i < self.layers.len(),
    {
        i + 1 < self.layers.len() ==> self.entry_size(i) == self.entry_size((i + 1) as nat)
            * self.num_entries((i + 1) as nat)
    }

    #[verifier(inline)]
    pub open spec(checked) fn entry_base(self, layer: nat, base: nat, idx: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
    {
        // base + idx * self.entry_size(layer)
        entry_base_from_index(base, idx, self.entry_size(layer))
    }

}


pub spec const x86_arch_spec: Arch = Arch {
    layers: seq![
        ArchLayer { entry_size: L0_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L1_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L2_ENTRY_SIZE as nat, num_entries: 512 },
        ArchLayer { entry_size: L3_ENTRY_SIZE as nat, num_entries: 512 },
    ],
};

pub open spec fn update_range<A>(s: Seq<A>, idx: int, new: Seq<A>) -> Seq<A>
{
    s.subrange(0, idx)
      + new
      + s.subrange(idx + new.len(), s.len() as int)
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
pub enum Step {
    MemOp { pte: Option<(nat, PTE)> },
    MemOpNA,
    MapStart,
    MapEnd,
    UnmapStart,
    UnmapEnd,
    Stutter,
}

#[allow(inconsistent_fields)]
pub enum ThreadState {
    Map { vaddr: nat, pte: PTE },
    Unmap { vaddr: nat, pte: Option<PTE> },
    Idle,
}

impl State {

    pub open spec fn vaddr_mapping_is_being_modified(self, c: Constants, va: nat) -> bool {
        exists|thread| {
            &&& c.valid_thread(thread)
            &&& match self.thread_state[thread] {
                ThreadState::Map { vaddr, pte } => between(va, vaddr, vaddr + pte.frame.size),
                ThreadState::Unmap { vaddr, pte: Some(pte) }
                    => between(va, vaddr, vaddr + pte.frame.size),
                _ => false,
            }
        }
    }

    pub open spec fn vaddr_mapping_is_being_modified_choose_thread(self, c: Constants, va: nat) -> nat
        recommends self.vaddr_mapping_is_being_modified(c, va)
    {
        choose|thread| {
            &&& c.valid_thread(thread)
            &&& match self.thread_state[thread] {
                ThreadState::Map { vaddr, pte } => between(va, vaddr, vaddr + pte.frame.size),
                ThreadState::Unmap { vaddr, pte: Some(pte) }
                    => between(va, vaddr, vaddr + pte.frame.size),
                _ => false,
            }
        }
    }

    pub open spec fn vaddr_mapping_is_being_modified_choose(self, c: Constants, va: nat) -> Option<(nat, PTE)>
        recommends self.vaddr_mapping_is_being_modified(c, va)
    {
        let thread = self.vaddr_mapping_is_being_modified_choose_thread(c, va);
        match self.thread_state[thread] {
            // Non-atomic pagefault
            ThreadState::Map { vaddr, pte }              => Some((vaddr, pte)),
            // Non-atomic successful translation
            ThreadState::Unmap { vaddr, pte: Some(pte) } => Some((vaddr, pte)),
            _                                            => arbitrary(),
        }
    }

}


pub open spec fn wf(c: Constants, s: State) -> bool {
    &&& forall|id: nat| id < c.thread_no <==> s.thread_state.contains_key(id)
    &&& s.mappings.dom().finite()
}

pub open spec fn is_in_mapped_region(phys_mem_size: nat, mappings: Map<nat, PTE>, vaddr: nat) -> bool {
    exists|base: nat, pte: PTE| {
        &&& #[trigger] mappings.contains_pair(base, pte)
        &&& between(vaddr, base, base + pte.frame.size)
        // TODO: This should arguably be something we require in step_Map_enabled so we'd know all
        // mapped memory is valid
        &&& pte.frame.base + (vaddr - base) < phys_mem_size
    }
}

impl Constants {

    pub open spec fn valid_thread(self, thread_id: nat) -> bool {
        thread_id < self.thread_no
    }

}


pub open spec fn state_unchanged_besides_thread_state_and_mem(
    s1: State,
    s2: State,
    thread_id: nat,
    thread_arguments: ThreadState,
) -> bool {
    &&& s2.thread_state === s1.thread_state.insert(thread_id, thread_arguments)
    &&& s2.mappings === s1.mappings
    &&& s2.sound == s1.sound
}

pub open spec fn unsound_state(s1: State, s2: State) -> bool {
    !s2.sound
}

pub open spec fn candidate_mapping_overlaps_inflight_vmem(
    inflightargs: Set<ThreadState>,
    base: nat,
    candidate_size: nat,
) -> bool {
    &&& exists|b: ThreadState|
        #![auto]
        {
            &&& inflightargs.contains(b)
            &&& match b {
                ThreadState::Map { vaddr, pte } => {
                    overlap(
                        MemRegion { base: vaddr, size: pte.frame.size },
                        MemRegion { base: base, size: candidate_size },
                    )
                },
                ThreadState::Unmap { vaddr, pte } => {
                    let size = if pte.is_some() {
                        pte.unwrap().frame.size
                    } else {
                        0
                    };
                    overlap(
                        MemRegion { base: vaddr, size: size },
                        MemRegion { base: base, size: candidate_size },
                    )
                },
                _ => { false },
            }
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

pub open spec fn step_MemOp(c: Constants, s1: State, s2: State, pte: Option<(nat, PTE)>, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MemOp { thread_id, vaddr, op }

    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] is Idle
    &&& aligned(vaddr, op.op_size())
    &&& op.valid_op_size()

    &&& match pte {
        Some((base, pte)) => {
            let paddr = pte.frame.base + (vaddr - base);
            // If pte is Some, it's an existing mapping that contains vaddr..
            &&& s1.mappings.contains_pair(base, pte)
            &&& between(vaddr, base, base + pte.frame.size)
            // .. and the result depends on the flags.
            &&& match op {
                MemOp::Store { new_value, result } => {
                    if paddr < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                        &&& result is Ok
                        &&& s2.mem === update_range(s1.mem, vaddr as int, new_value)
                    } else {
                        &&& result is Pagefault
                        &&& s2.mem === s1.mem
                    }
                },
                MemOp::Load { is_exec, result, .. } => {
                    &&& s2.mem === s1.mem
                    &&& if paddr < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                        &&& result is Value
                        &&& result->0 == s1.mem.subrange(vaddr as int, vaddr + op.op_size() as int)
                    } else {
                        &&& result is Pagefault
                    }
                },
            }
        },
        None => {
            // If pte is None, no mapping containing vaddr exists..
            &&& !is_in_mapped_region(c.phys_mem_size, s1.mappings, vaddr)
            // .. and the result is always a pagefault and an unchanged memory.
            &&& s2.mem === s1.mem
            &&& op.is_pagefault()
        },
    }
    &&& s2.mappings === s1.mappings
    &&& s2.thread_state === s1.thread_state
    &&& s2.sound == s1.sound
}

pub open spec fn step_MemOpNA(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MemOp { thread_id, vaddr, op }

    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] is Idle
    &&& aligned(vaddr, op.op_size())
    &&& op.valid_op_size()

    &&& s1.vaddr_mapping_is_being_modified(c, vaddr)
    &&& {
    let pte = s1.vaddr_mapping_is_being_modified_choose(c, vaddr);
    &&& match pte {
        Some((base, pte)) => {
            ||| (s2.mem === s1.mem && op.is_pagefault())
            ||| ({
                let paddr = pte.frame.base + (vaddr - base);
                // the result depends on the flags
                &&& match op {
                    MemOp::Store { new_value, result } => {
                        if paddr < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                            &&& result is Ok
                            &&& s2.mem === update_range(s1.mem, vaddr as int, new_value)
                        } else {
                            &&& result is Pagefault
                            &&& s2.mem === s1.mem
                        }
                    },
                    MemOp::Load { is_exec, result, .. } => {
                        &&& s2.mem === s1.mem
                        &&& if paddr < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                            &&& result is Value
                            &&& result->0 == s1.mem.subrange(vaddr as int, vaddr + op.op_size() as int)
                        } else {
                            &&& result is Pagefault
                        }
                    },
                }
            })
        },
        None => {
            &&& s2.mem === s1.mem
            &&& op.is_pagefault()
        },
    }
    &&& s2.mappings === s1.mappings
    &&& s2.thread_state === s1.thread_state
    &&& s2.sound == s1.sound
    }

}

pub open spec fn step_Map_sound(
    mappings: Map<nat, PTE>,
    inflights: Set<ThreadState>,
    vaddr: nat,
    pte: PTE,
) -> bool {
    &&& !candidate_mapping_overlaps_inflight_vmem(inflights, vaddr, pte.frame.size)
    &&& !candidate_mapping_overlaps_existing_pmem(mappings, pte)
    &&& !candidate_mapping_overlaps_inflight_pmem(inflights, pte)
}

pub open spec fn step_Map_enabled(
    inflight: Set<ThreadState>,
    map: Map<nat, PTE>,
    vaddr: nat,
    pte: PTE,
) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& pte.frame.base <= MAX_PHYADDR
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& {  // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
}

pub open spec fn step_MapStart(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MapStart { thread_id, vaddr, pte }
    &&& step_Map_enabled(s1.thread_state.values(), s1.mappings, vaddr, pte)
    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] === ThreadState::Idle
    &&& if step_Map_sound(s1.mappings, s1.thread_state.values(), vaddr, pte) {
        state_unchanged_besides_thread_state_and_mem(s1, s2, thread_id, ThreadState::Map { vaddr, pte })
        && (if candidate_mapping_overlaps_existing_vmem(s1.mappings, vaddr, pte) {
            s1.mem == s2.mem
        } else {
            forall|vaddr: nat|  #[trigger] is_in_mapped_region(c.phys_mem_size, s1.mappings, vaddr) ==> s2.mem[vaddr as int] === s1.mem[vaddr as int]
        })
    } else {
        unsound_state(s1, s2)
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

pub open spec fn step_Unmap_sound(s1: State, vaddr: nat, pte_size: nat) -> bool {
    !candidate_mapping_overlaps_inflight_vmem(s1.thread_state.values(), vaddr, pte_size)
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& vaddr < x86_arch_spec.upper_vaddr(0, 0)
    &&& { // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

pub open spec fn step_UnmapStart(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::UnmapStart { thread_id, vaddr }
    &&& {
    let pte = if s1.mappings.contains_key(vaddr) { Some(s1.mappings[vaddr]) } else { Option::None };
    let pte_size = if pte is Some { pte.unwrap().frame.size } else { 0 };
    &&& step_Unmap_enabled(vaddr)
    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] === ThreadState::Idle
    &&& if step_Unmap_sound(s1, vaddr, pte_size) {
            &&& s2.thread_state === s1.thread_state.insert(thread_id, ThreadState::Unmap { vaddr, pte })
            &&& s2.mappings == if pte is None { s1.mappings } else { s1.mappings.remove(vaddr) }
            &&& s2.sound == s1.sound
            &&& s2.mem === s1.mem
        } else {
            unsound_state(s1, s2)
        }
    }
}

pub open spec fn step_UnmapEnd(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::UnmapEnd { thread_id, vaddr, result }

    &&& c.valid_thread(thread_id)
    &&& s1.thread_state[thread_id] matches ThreadState::Unmap { vaddr: v2, pte }
    &&& vaddr == v2
    &&& pte is Some <==> result is Ok

    &&& s2.thread_state === s1.thread_state.insert(thread_id, ThreadState::Idle)
    &&& s2.sound == s1.sound
    &&& s2.mappings === s1.mappings
    &&& forall|vaddr: nat|  #[trigger] is_in_mapped_region(c.phys_mem_size, s2.mappings, vaddr) ==> s2.mem[vaddr as int] === s1.mem[vaddr as int]
}

pub open spec fn step_Stutter(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl is Tau
    &&& s1 === s2
}

pub open spec fn next_step(c: Constants, s1: State, s2: State, step: Step, lbl: RLbl) -> bool {
    if s1.sound {
        match step {
            Step::MemOp { pte } => step_MemOp(c, s1, s2, pte, lbl),
            Step::MemOpNA       => step_MemOpNA(c, s1, s2, lbl),
            Step::MapStart      => step_MapStart(c, s1, s2, lbl),
            Step::MapEnd        => step_MapEnd(c, s1, s2, lbl),
            Step::UnmapStart    => step_UnmapStart(c, s1, s2, lbl),
            Step::UnmapEnd      => step_UnmapEnd(c, s1, s2, lbl),
            Step::Stutter       => step_Stutter(c, s1, s2, lbl),
        }
    } else {
        !s2.sound
    }
}

pub open spec fn next(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    exists|step: Step| next_step(c, s1, s2, step, lbl)
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

pub proof fn next_step_preserves_inv(c: Constants, s1: State, s2: State, lbl: RLbl)
    requires
        next(c, s1, s2, lbl),
        s1.sound ==> inv(c, s1),
    ensures
        s2.sound ==> inv(c, s2),
{
    if s1.sound {
        let p = choose|step: Step| next_step(c, s1, s2, step, lbl);
        match p {
            Step::UnmapStart => unmap_start_preserves_inv(c, s1, s2, lbl),
            Step::UnmapEnd => {
                let thread_id = lbl->UnmapEnd_thread_id;
                assert(s2.thread_state.values().subset_of(s1.thread_state.values().insert(ThreadState::Idle)));
                //lemma_mem_domain_from_mapping_finite(c.phys_mem_size, s2.mappings);
                insert_non_map_preserves_unique(s1.thread_state, thread_id, ThreadState::Idle);
            },
            Step::MapStart => map_start_preserves_inv(c, s1, s2, lbl),
            Step::MapEnd  => map_end_preserves_inv(c, s1, s2, lbl),
            _ => {},
        }
    } else {
        assert(!s2.sound);
    }
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

	#[verifier::external_body]
#[verifier::spinoff_prover]
pub proof fn unmap_start_preserves_inv(c: Constants, s1: State, s2: State, lbl: RLbl)
    requires
        step_UnmapStart(c, s1, s2, lbl),
        s1.sound ==> inv(c, s1),
        s1.sound,
        s1.thread_state.dom().contains(lbl->UnmapStart_thread_id),
    ensures
        s2.sound ==> inv(c, s2),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn map_start_preserves_inv(c: Constants, s1: State, s2: State, lbl: RLbl)
    requires
        step_MapStart(c, s1, s2, lbl),
        s1.sound ==> inv(c, s1),
        s1.sound,
        s1.thread_state.dom().contains(lbl->MapStart_thread_id),
    ensures
        s2.sound ==> inv(c, s2),
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub proof fn map_end_preserves_inv(c: Constants, s1: State, s2: State, lbl: RLbl)
    requires
        step_MapEnd(c, s1, s2, lbl),
        s1.sound ==> inv(c, s1),
        s1.sound,
        s1.thread_state.contains_key(lbl->MapEnd_thread_id),
    ensures
        s2.sound ==> inv(c, s2),
	{
		unimplemented!()
	}


}
