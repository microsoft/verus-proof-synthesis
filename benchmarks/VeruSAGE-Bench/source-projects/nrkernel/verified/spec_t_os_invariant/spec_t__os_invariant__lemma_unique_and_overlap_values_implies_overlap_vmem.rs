use vstd::prelude::*;
use crate::defs::*;

fn main() {}

verus!{

global size_of usize == 8;

pub mod rl1 {
    use vstd::prelude::*;
    use crate::defs::*;
    use crate::PTMem;
    use crate::rl3::Writes;

// File: spec_t/mmu/rl1.rs
pub struct State {
    pub happy: bool,
    /// Byte-indexed physical (non-page-table) memory
    pub phys_mem: Seq<u8>,
    /// Page table memory
    pub pt_mem: PTMem,
    /// Per-node state (TLBs)
    pub tlbs: Map<Core, Map<usize, PTE>>,
    pub writes: Writes,
    /// Tracks the virtual addresses and entries for which we may see non-atomic results.
    /// If polarity is positive, translations may non-atomically fail.
    /// If polarity is negative, translations may non-atomically succeed.
    pub pending_maps: Map<usize, PTE>,
    pub pending_unmaps: Map<usize, PTE>,
    pub polarity: crate::Polarity,
}
}

pub mod rl2 {
    use vstd::prelude::*;
    use crate::defs::*;
    use crate::rl3::Writes;
    use crate::{Walk, PTMem};

// File: spec_t/mmu/rl2.rs
pub struct State {
    pub happy: bool,
    /// Byte-indexed physical (non-page-table) memory
    pub phys_mem: Seq<u8>,
    /// Page table memory
    pub pt_mem: PTMem,
    /// Per-node state (TLBs)
    pub tlbs: Map<Core, Map<usize, PTE>>,
    /// In-progress page table walks
    pub walks: Map<Core, Set<Walk>>,
    /// Store buffers
    pub sbuf: Map<Core, Seq<(usize, usize)>>,
    pub writes: Writes,
    pub polarity: crate::Polarity,
    pub hist: History,
}

pub struct History {
    pub pending_maps: Map<usize, PTE>,
    pub pending_unmaps: Map<usize, PTE>,
}

impl State {

    pub open spec fn core_mem(self, core: Core) -> crate::PTMem {
        self.pt_mem.write_seq(self.sbuf[core])
    }

    #[verifier(inline)]
    pub open spec fn writer_mem(self) -> crate::PTMem {
        self.core_mem(self.writes.core)
    }

}

pub mod refinement {

    impl crate::rl2::State {

        pub open spec fn interp(self) -> crate::rl1::State {
            crate::rl1::State {
                happy: self.happy,
                pt_mem: self.writer_mem(),
                phys_mem: self.phys_mem,
                tlbs: self.tlbs,
                writes: self.writes,
                pending_maps: self.hist.pending_maps,
                pending_unmaps: self.hist.pending_unmaps,
                polarity: self.polarity,
            }
        }
    }
}

}

pub mod rl3 {
    use vstd::prelude::*;
    use crate::defs::*;
    use crate::{Polarity, Walk, PTMem};

// File: spec_t/mmu/rl3.rs
pub struct State {
    /// Byte-indexed physical (non-page-table) memory
    phys_mem: Seq<u8>,
    /// Page table memory
    pt_mem: PTMem,
    /// Per-node state (TLBs)
    tlbs: Map<Core, Map<usize, PTE>>,
    /// In-progress page table walks
    walks: Map<Core, Set<Walk>>,
    /// Translation caches
    cache: Map<Core, Set<Walk>>,
    /// Store buffers
    sbuf: Map<Core, Seq<(usize, usize)>>,
    /// History variables. These do not influence the transitions in any way. Neither in enabling
    /// conditions nor in state updates. We only use these during the refinement.
    hist: History,
}

pub struct History {
    pub happy: bool,
    /// All partial walks since the last invlpg
    pub walks: Map<Core, Set<Walk>>,
    pub writes: Writes,
    pub pending_maps: Map<usize, PTE>,
    pub pending_unmaps: Map<usize, PTE>,
    pub polarity: Polarity,
}


pub struct Writes {
    /// Current writer core. If `all` is non-empty, all those writes were done by this core.
    pub core: Core,
    /// Tracks all writes that may cause stale reads due to TSO. Set of addresses. Gets cleared
    /// when the corresponding core drains its store buffer.
    pub tso: Set<usize>,
    /// Tracks staleness resulting from non-atomicity and translation caching. Cleared by invlpg if
    /// store buffers are empty.
    pub nonpos: Set<Core>,
}

pub mod refinement {

    impl crate::rl3::State {

	#[verifier::external_body]
        pub closed spec fn interp(self) -> crate::rl2::State {
		unimplemented!()
	}
    }

    pub mod to_rl1{

        impl crate::rl3::State{

            pub open spec fn view(self) -> crate::rl1::State {
                self.interp().interp()
            }
        }
    }

}
}



// File: spec_t/mmu/pt_mem.rs
pub struct PTMem {
    pub mem: Map<usize, usize>,
    pub pml4: usize,
}

impl PTMem {

    pub open spec fn write(self, addr: usize, value: usize) -> PTMem {
        PTMem {
            mem: self.mem.insert(addr, value),
            pml4: self.pml4,
        }
    }

    pub open spec fn write_seq(self, writes: Seq<(usize, usize)>) -> Self {
        writes.fold_left(self, |acc: PTMem, wr: (_, _)| acc.write(wr.0, wr.1))
    }

    #[verifier::external_body]
    pub open spec fn view(self) -> Map<usize,PTE> {
		unimplemented!()
    }


}



// File: spec_t/mmu/translation.rs
pub ghost enum GPDE {
    Directory {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        RW: bool,
        /// User/supervisor; user-mode accesses are not allowed to the page controlled by this entry
        US: bool,
        /// Page-level write-through
        PWT: bool,
        /// Page-level cache disable
        PCD: bool,
        ///// Accessed; indicates whether software has accessed the page referenced by this entry
        //A: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        XD: bool,
    },
    Page {
        addr: usize,
        /// Present; must be 1 to map a page or reference a directory
        P: bool,
        /// Read/write; if 0, writes may not be allowed to the page controlled by this entry
        RW: bool,
        /// User/supervisor; if 0, user-mode accesses are not allowed to the page controlled by this entry
        US: bool,
        /// Page-level write-through
        PWT: bool,
        /// Page-level cache disable
        PCD: bool,
        ///// Accessed; indicates whether software has accessed the page referenced by this entry
        //A: bool,
        ///// Dirty; indicates whether software has written to the page referenced by this entry
        //D: bool,
        // /// Page size; must be 1 (otherwise, this entry references a directory)
        // PS: Option<bool>,
        // PS is entirely determined by the Page variant and the layer
        /// Global; if CR4.PGE = 1, determines whether the translation is global; ignored otherwise
        G: bool,
        /// Indirectly determines the memory type used to access the page referenced by this entry
        PAT: bool,
        /// If IA32_EFER.NXE = 1, execute-disable (if 1, instruction fetches are not allowed from
        /// the page controlled by this entry); otherwise, reserved (must be 0)
        XD: bool,
    },
    /// An `Invalid` entry is an entry that does not contain a valid mapping. I.e. the entry is
    /// either empty or has a bit set that the intel manual designates as must-be-zero. Both empty
    /// and invalid entries cause a page fault if used during translation.
    Invalid,
}

pub mod defs{

use vstd::prelude::*;

// File: spec_t/mmu/defs.rs
pub const X86_NUM_LAYERS: usize = 4;

pub const X86_NUM_ENTRIES: usize = 512;

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

pub open spec fn candidate_mapping_in_bounds_pmem(c: crate::Constants, pte: PTE) -> bool {
    pte.frame.base + pte.frame.size <= c.range_mem.1
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

pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

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


pub open spec fn nat_keys<V>(m: Map<usize, V>) -> Map<nat, V> {
    Map::new(|k: nat| k <= usize::MAX && m.contains_key(k as usize), |k: nat| m[k as usize])
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

pub struct State {
    pub mmu: crate::rl3::State,
    pub os_ext: crate::os_ext::State,
    pub core_states: Map<Core, CoreState>,
    /// `sound` is a history variable. It doesn't affect the behavior of the state machine but is
    /// used in the refinement.
    pub sound: bool,
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

    pub open spec fn is_in_crit_sect(self) -> bool {
        match self {
            CoreState::Idle
            | CoreState::MapWaiting { .. }
            | CoreState::UnmapWaiting { .. } => false,
            _ => true,
        }
    }

    pub open spec fn is_map(self) -> bool {
        match self {
            CoreState::MapWaiting { .. }
            | CoreState::MapExecuting { .. }
            | CoreState::MapDone { .. } => true,
            _ => false,
        }
    }

    #[verifier(inline)]
    pub open spec fn is_idle(self) -> bool {
        self is Idle
    }

}


impl Constants {

    pub open spec fn valid_ult(self, ult_id: nat) -> bool {
        ult_id < self.ult_no
    }

    pub open spec fn valid_core(self, core: Core) -> bool {
        self.common.valid_core(core)
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

    pub open spec fn has_pte(self, pt: Map<nat, PTE>) -> bool
    {
        match self {
            CoreState::MapWaiting { pte, .. }
            | CoreState::MapExecuting { pte, .. }
            | CoreState::MapDone { pte, .. } => {
                true
            }
            CoreState::UnmapWaiting { vaddr, .. }  
            | CoreState::UnmapExecuting { vaddr, result: None, .. } => pt.contains_key(vaddr),
            CoreState::UnmapExecuting { result: Some(Ok(_)), .. }
            | CoreState::UnmapOpDone { result: Ok(_), .. }
            | CoreState::UnmapShootdownWaiting { result: Ok(_), .. } => true,
            _ => false,
        }
    }

    pub open spec fn PTE(self) -> PTE
        recommends self.is_map(),
    {
        match self {
            CoreState::MapWaiting { pte, .. }
            | CoreState::MapExecuting { pte, .. }
            | CoreState::MapDone { pte, .. }
            | CoreState::UnmapExecuting { result: Some(Ok(pte)), .. }
            | CoreState::UnmapOpDone { result: Ok(pte), .. }
            | CoreState::UnmapShootdownWaiting { result: Ok(pte), .. }
            => {
                pte
            }
            _ => arbitrary(),
        }
    }

}


impl State {

    pub open spec fn interp_pt_mem(self) -> Map<nat, PTE> {
        crate::defs::nat_keys(self.mmu@.pt_mem@)
    }

    pub open spec fn valid_ids(self, c: Constants) -> bool {
        forall|core: Core|
            c.valid_core(core) ==> match self.core_states[core] {
                CoreState::MapWaiting { ult_id, .. }
                | CoreState::MapExecuting { ult_id, .. }
                | CoreState::MapDone { ult_id, .. }
                | CoreState::UnmapWaiting { ult_id, .. }
                | CoreState::UnmapExecuting { ult_id, .. }
                | CoreState::UnmapOpDone { ult_id, .. }
                | CoreState::UnmapShootdownWaiting { ult_id, .. } => {
                    &&& c.valid_ult(ult_id)
                    &&& c.ult2core[ult_id] === core
                },
                CoreState::Idle => true,
            }
    }

    pub open spec fn inv_inflight_pte_wf(self, c: Constants) -> bool {
        forall|core: Core| #![auto] c.valid_core(core) && self.core_states[core].has_pte(self.interp_pt_mem()) 
        && !(self.core_states[core] matches CoreState::UnmapExecuting {result: None, ..})
        && !(self.core_states[core] is UnmapWaiting)==> {
            let pte = self.core_states[core].PTE();
            let vaddr = self.core_states[core].vaddr();
            &&& aligned(vaddr, pte.frame.size)
            &&& aligned(pte.frame.base, pte.frame.size)
            &&& candidate_mapping_in_bounds(vaddr, pte)
            &&& candidate_mapping_in_bounds_pmem(c.common, pte)
            &&& (pte.frame.size == L1_ENTRY_SIZE
                || pte.frame.size == L2_ENTRY_SIZE
                || pte.frame.size == L3_ENTRY_SIZE)
        }
    }

    pub open spec fn inv_mapped_pte_wf(self, c: Constants) -> bool {
        forall|vaddr| self.interp_pt_mem().contains_key(vaddr) ==> {
            let pte = self.interp_pt_mem()[vaddr];
            &&& aligned(vaddr, pte.frame.size)
            &&& aligned(pte.frame.base, pte.frame.size)
            &&& candidate_mapping_in_bounds(vaddr, pte)
            &&& candidate_mapping_in_bounds_pmem(c.common, pte)
            &&& (pte.frame.size == L1_ENTRY_SIZE
                || pte.frame.size == L2_ENTRY_SIZE
                || pte.frame.size == L3_ENTRY_SIZE)
        }
    }

    pub open spec fn inv_successful_maps(self, c: Constants) -> bool {
        forall|core: Core| c.valid_core(core) ==>
            match self.core_states[core] {
                CoreState::MapDone { vaddr, pte, result: Result::Ok(_), .. }
                    => self.interp_pt_mem().contains_pair(vaddr, pte),
                _ => true,
            }
    }

    pub open spec fn inv_unsuccessful_maps(self, c: Constants) -> bool {
        forall|core: Core| c.valid_core(core) ==>
            match self.core_states[core] {
                CoreState::MapDone { vaddr, pte, result: Result::Err(_), .. }
                    => candidate_mapping_overlaps_existing_vmem(self.interp_pt_mem(), vaddr, pte),
                _ => true,
            }
    }

    pub open spec fn inv_overlap_of_mapped_maps(self, c: Constants) -> bool {
        forall|core: Core| c.valid_core(core) ==>
            match self.core_states[core] {
                CoreState::MapDone { vaddr, pte, result: Result::Ok(_), .. }
                    => !candidate_mapping_overlaps_existing_vmem(self.interp_pt_mem().remove(vaddr), vaddr, pte),
                CoreState::MapDone { vaddr, pte, result: Result::Err(_), .. }
                    => candidate_mapping_overlaps_existing_vmem(self.interp_pt_mem(), vaddr, pte),
                _ => true,
            }
    }

    pub open spec fn inv_successful_unmaps(self, c: Constants) -> bool {
        forall|core: Core| c.valid_core(core) ==>
            match self.core_states[core] {
                CoreState::UnmapExecuting { vaddr, result: Some(_), .. }
                | CoreState::UnmapOpDone { vaddr, .. }
                | CoreState::UnmapShootdownWaiting { vaddr, .. }
                    => !self.interp_pt_mem().contains_key(vaddr),
                _ => true,
            }
    }

    pub open spec fn inv_lock(self, c: Constants) -> bool {
        forall|core: Core|
            (self.os_ext.lock === Some(core) <==> #[trigger] c.valid_core(core) && self.core_states[core].is_in_crit_sect())
    }

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& self.valid_ids(c)
        &&& forall|id: nat| #[trigger] c.valid_ult(id) <==> c.ult2core.contains_key(id)
        &&& forall|id: nat| c.valid_ult(id) ==> #[trigger] c.valid_core(c.ult2core[id])
        &&& forall|core: Core| c.valid_core(core) <==> #[trigger] self.core_states.contains_key(core)
    }

    pub open spec fn inv_basic(self, c: Constants) -> bool {
        &&& self.wf(c)
        &&& self.inv_inflight_pte_wf(c)
        &&& self.inv_mapped_pte_wf(c)
        &&& self.inv_successful_unmaps(c)
        &&& self.inv_unsuccessful_maps(c)
        &&& self.inv_successful_maps(c)
        &&& self.inv_overlap_of_mapped_maps(c)
        &&& self.inv_lock(c)
    }

    pub open spec fn inv_inflight_map_no_overlap_inflight_vmem(self, c: Constants) -> bool {
        forall|core1: Core, core2: Core|
            (c.valid_core(core1) && c.valid_core(core2)
                && !self.core_states[core1].is_idle() && !self.core_states[core2].is_idle()
                && overlap(
                MemRegion {
                    base: self.core_states[core1].vaddr(),
                    size: self.core_states[core1].pte_size(self.interp_pt_mem()),
                },
                MemRegion {
                    base: self.core_states[core2].vaddr(),
                    size: self.core_states[core2].pte_size(self.interp_pt_mem()),
                },
            )) ==> core1 === core2
    }

}
}

pub mod os_ext {
    use vstd::prelude::*;
    use crate::defs::*;

// File: spec_t/os_ext.rs
pub struct State {
    pub lock: Option<Core>,
    pub shootdown_vec: ShootdownVector,
    pub allocated: Set<MemRegion>,
}

pub struct ShootdownVector {
    pub vaddr: nat,
    pub open_requests: Set<Core>,
}
}

// File: spec_t/mmu/mod.rs
pub enum Polarity {
    Mapping,
    Unmapping,
    // Protect,
}

pub struct Walk {
    pub vaddr: usize,
    pub path: Seq<(usize, GPDE)>,
    pub complete: bool,
}

pub struct Constants {
    pub node_count: nat,
    pub core_count: nat,
    /// The range of memory used for the page table
    pub range_ptmem: (nat, nat),
    /// The range of memory used for the user memory
    pub range_mem: (nat, nat),
    pub phys_mem_size: nat,
}

impl Constants {

	#[verifier::external_body]
    pub open spec fn valid_core(self, core: Core) -> bool {
		unimplemented!()
	}
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

pub proof fn lemma_unique_and_overlap_values_implies_overlap_vmem(
    c: os::Constants,
    s: os::State,
)
    requires
        unique_CoreStates(s.core_states),
        no_overlap_vmem_values(s.core_states, s.interp_pt_mem()),
        s.inv_basic(c),
    ensures
        s.inv_inflight_map_no_overlap_inflight_vmem(c),
{
    assert(forall|core| #[trigger] c.valid_core(core) ==> s.core_states.contains_key(core));
}


}
