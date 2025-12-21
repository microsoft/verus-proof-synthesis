use vstd::prelude::*;
use crate::defs::Core;

fn main() {}

verus!{
global size_of usize == 8;

// File: spec_t/mmu/rl1.rs
pub mod rl1 {

use vstd::prelude::*;
use crate::{Polarity, Constants, PTMem};
use crate::defs::{Core, PTE, aligned};
use crate::rl3::Writes;

// This mod contains refinement layer 1 of the MMU. Compared to layer 2, it removes store buffers
// and defines an atomic semantics to page table walks. This is the most abstract version of the
// MMU model.

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
    pub polarity: Polarity,
}

pub open spec fn init(pre: State, c: Constants) -> bool {
    &&& pre.happy
    &&& pre.tlbs === Map::new(|core| c.valid_core(core), |core| map![])
    &&& pre.writes.tso === set![]
    &&& pre.writes.nonpos === set![]
    &&& pre.pending_maps === map![]
    &&& pre.pending_unmaps === map![]
    &&& pre.polarity === Polarity::Mapping

    &&& c.valid_core(pre.writes.core)
    &&& pre.pt_mem.mem === Map::new(|va| aligned(va as nat, 8) && c.in_ptmem_range(va as nat, 8), |va| 0)
    &&& aligned(pre.pt_mem.pml4 as nat, 4096)
    &&& c.memories_disjoint()
    &&& pre.phys_mem.len() == c.range_mem.1
    &&& c.in_ptmem_range(pre.pt_mem.pml4 as nat, 4096)
}
}


// File: spec_t/mmu/rl2.rs
pub mod rl2{
use vstd::prelude::*;
use crate::{Core, PTMem, Polarity};
use crate::rl3::Writes;
use crate::defs::{PTE};
use crate::Walk;

// This file contains refinement layer 2 of the MMU. Compared to layer 3, it expresses translation
// caching and non-atomic walks as a single concept, and replaces the explicit havoc-ing of
// dirty/accessed bits with underspecified reads.

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
    pub polarity: Polarity,
    pub hist: History,
}

pub struct History {
    pub pending_maps: Map<usize, PTE>,
    pub pending_unmaps: Map<usize, PTE>,
}

impl State {

    pub open spec fn core_mem(self, core: Core) -> PTMem {
        self.pt_mem.write_seq(self.sbuf[core])
    }

    #[verifier(inline)]
    pub open spec fn writer_mem(self) -> PTMem {
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

// File: spec_t/mmu/rl3.rs
pub mod rl3{
    use vstd::prelude::*;
    use crate::defs::*;
    use crate::*;

// Trusted: This file defines the assumed semantics of the memory translation hardware as a state
// machine.
//
// This file contains refinement layer 3 of the MMU. This is the most concrete MMU model, i.e. the
// behavior we assume of the hardware.
//
// Most of the definitions in this file are `closed`. We reason about the behavior of this state
// machine exclusively in terms of the more abstract MMU models it refines.

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

	#[verifier::external_body]
pub closed spec fn init(pre: State, c: crate::Constants) -> bool {
		unimplemented!()
	}

pub mod refinement {

    impl crate::rl3::State {

	#[verifier::external_body]
        pub closed spec fn interp(self) -> crate::rl2::State {
		unimplemented!()
	}
    }

    pub mod to_rl1 {
//! Machinery to lift rl3 semantics to rl1 (interp twice and corresponding lemmas), which we use for
//! reasoning about the OS state machine.

        impl crate::rl3::State {

            pub open spec fn view(self) -> crate::rl1::State {
                self.interp().interp()
            }
        }


        #[verifier::external_body]
        pub proof fn init_refines(pre: crate::rl3::State, c: crate::Constants)
            requires crate::rl3::init(pre, c),
            ensures crate::rl1::init(pre@, c),
	{
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

    pub open spec fn read(self, addr: usize) -> usize {
        self.mem[addr]
    }

    pub open spec fn write_seq(self, writes: Seq<(usize, usize)>) -> Self {
        writes.fold_left(self, |acc: PTMem, wr: (_, _)| acc.write(wr.0, wr.1))
    }

	#[verifier::external_body]
    pub open spec fn view(self) -> Map<usize, crate::defs::PTE> {
		unimplemented!()
	}


}

// File: spec_t/mmu/translation.rs
// Trusted: This file defines the semantics of how page table entries are interpreted by the
// hardware. This is only the semantics of how we go from bits to an interpretation; The hardware
// model in rl3.rs models the non-atomic nature of page table walks + caching + ..

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


// File: spec_t/mmu/defs.rs
pub mod defs {
    use vstd::prelude::*;

pub const X86_NUM_ENTRIES: usize = 512;

// The maximum physical address width is between 32 and 52 bits.
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


pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 512 * 512 * 4096;

pub spec const MAX_BASE: nat = X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES as nat);

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

pub open spec fn nat_keys<V>(m: Map<usize, V>) -> Map<nat, V> {
    Map::new(|k: nat| k <= usize::MAX && m.contains_key(k as usize), |k: nat| m[k as usize])
}
}

pub mod os {
    use vstd::prelude::*;
    use crate::defs::*;

// File: spec_t/os.rs

// describes how the whole system behaves

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

    pub open spec fn is_map(self) -> bool {
        match self {
            CoreState::MapWaiting { .. }
            | CoreState::MapExecuting { .. }
            | CoreState::MapDone { .. } => true,
            _ => false,
        }
    }

    pub open spec fn is_unmapping(self) -> bool {
        match self {
            CoreState::UnmapWaiting { .. }
            | CoreState::UnmapExecuting { .. }
            | CoreState::UnmapOpDone { .. }
            | CoreState::UnmapShootdownWaiting { .. } => true,
            _ => false,
        }
    }

    pub open spec fn unmap_vaddr(self) -> nat
        recommends self.is_unmapping()
    {
        match self {
            CoreState::UnmapWaiting { vaddr, .. }
            | CoreState::UnmapExecuting { vaddr, .. }
            | CoreState::UnmapOpDone { vaddr, .. }
            | CoreState::UnmapShootdownWaiting { vaddr, .. } => vaddr,
            _ => arbitrary(),
        }
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


pub open spec fn init(c: Constants, s: State) -> bool {
    // hardware stuff
    //&&& s.interp_pt_mem() === Map::empty()
    &&& crate::rl3::init(s.mmu, c.common)
    &&& crate::os_ext::init(s.os_ext, c.common)
    // We start with a single directory already allocated for PML4
    &&& s.os_ext.allocated === set![MemRegion { base: s.mmu@.pt_mem.pml4 as nat, size: 4096 }]
    // and that directory is empty
    &&& forall|i: usize| 0 <= i < 512 ==> #[trigger] s.mmu@.pt_mem.read(add(s.mmu@.pt_mem.pml4, mul(i, 8))) == 0
    //wf of ult2core mapping
    &&& forall|id: nat| #[trigger] c.valid_ult(id) <==> c.ult2core.contains_key(id)
    &&& forall|id: nat| c.valid_ult(id) ==> #[trigger] c.valid_core(c.ult2core[id])
    //core_state
    &&& forall|core: Core| c.valid_core(core) <==> #[trigger] s.core_states.contains_key(core)
    &&& forall|core: Core| #[trigger] c.valid_core(core) ==> s.core_states[core] === CoreState::Idle
    //sound
    &&& s.sound
}

impl CoreState {

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

    pub open spec fn is_unmap_vaddr_core(self, core: Core, vaddr: nat) -> bool {
        self.core_states.contains_key(core) && match self.core_states[core] {
            CoreState::UnmapExecuting { vaddr: vaddr1, result: Some(result), .. } => {
                (result is Ok) && (vaddr1 === vaddr)
            },
            CoreState::UnmapOpDone { vaddr: vaddr1, result, .. } => {
                (result is Ok) && (vaddr1 === vaddr)
            },
            CoreState::UnmapShootdownWaiting { vaddr: vaddr1, result, .. } => {
                (result is Ok) && (vaddr1 === vaddr)
            },
            _ => false,
        }
    }

    pub open spec fn is_unmap_vaddr(self, vaddr: nat) -> bool {
        exists|core: Core| self.is_unmap_vaddr_core(core, vaddr)
    }

    pub open spec fn unmap_vaddr_set(self) -> Set<nat> {
        Set::new(|vaddr: nat| self.is_unmap_vaddr(vaddr))
    }

    pub open spec fn inv_tlb_wf(self, c: Constants) -> bool {
        forall|core| #![auto] c.valid_core(core) && self.core_states[core].is_unmapping()
            ==> self.core_states[core].unmap_vaddr() < MAX_BASE
    }

    pub open spec fn inv_shootdown_wf(self, c: Constants) -> bool {
        forall|dispatcher: Core | (#[trigger] c.valid_core(dispatcher) && self.core_states[dispatcher] is UnmapShootdownWaiting) 
        ==> self.core_states[dispatcher]->UnmapShootdownWaiting_vaddr
                == self.os_ext.shootdown_vec.vaddr
    }

    pub open spec fn shootdown_cores_valid(self, c: Constants) -> bool {
        forall|core| #[trigger]
            self.os_ext.shootdown_vec.open_requests.contains(core) ==> c.valid_core(core)
    }

    pub open spec fn all_cores_nonpos_before_shootdown(self, c: Constants) -> bool {
        (self.os_ext.lock is Some
            && self.core_states[self.os_ext.lock->Some_0] matches CoreState::UnmapExecuting { result: Some(_), .. })
        ==> self.mmu@.writes.nonpos == Set::new(|core| c.valid_core(core))
    }

    pub open spec fn successful_invlpg(self, c: Constants) -> bool {
        forall|dispatcher: Core, handler: Core|
            #[trigger] c.valid_core(dispatcher)
            && c.valid_core(handler) 
            && self.core_states[dispatcher] is UnmapShootdownWaiting
            && !(#[trigger] self.mmu@.writes.nonpos.contains(handler))
                ==> !self.mmu@.tlbs[handler].contains_key(
                        (self.core_states[dispatcher]->UnmapShootdownWaiting_vaddr) as usize)
    }

    pub open spec fn successful_IPI(self, c: Constants) -> bool {
        forall|dispatcher: Core, handler: Core|
            #[trigger] c.valid_core(dispatcher)
            && c.valid_core(handler) 
            && self.core_states[dispatcher] is UnmapShootdownWaiting
            && !(#[trigger] self.os_ext.shootdown_vec.open_requests.contains(handler))
                ==> {
                    &&& !self.mmu@.tlbs[handler].contains_key(
                        (self.core_states[dispatcher]->UnmapShootdownWaiting_vaddr) as usize)
                    &&& !self.mmu@.writes.nonpos.contains(handler)
                }
    }

    pub open spec fn TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(self, c: Constants) -> bool {
        forall|core: Core| #[trigger] c.valid_core(core)
            ==> self.mmu@.tlbs[core].dom().map(|v| v as nat).subset_of(
                self.interp_pt_mem().dom().union(self.unmap_vaddr_set()))
    }

    pub open spec fn TLB_interp_pt_mem_agree(self, c: Constants) -> bool {
        forall|core: Core, v: usize|
            #[trigger] c.valid_core(core)
            && #[trigger] self.mmu@.tlbs[core].dom().contains(v)
            && self.interp_pt_mem().dom().contains(v as nat)
            ==> self.mmu@.tlbs[core][v] == self.interp_pt_mem()[v as nat]
    }

    pub open spec fn TLB_unmap_agree(self, c: Constants) -> bool {
        forall|core: Core, core2: Core, v: usize|
            #[trigger] c.valid_core(core)
            && #[trigger] self.mmu@.tlbs[core].dom().contains(v)
            && #[trigger] c.valid_core(core2)
            && self.is_unmap_vaddr_core(core2, v as nat)
            ==> self.mmu@.tlbs[core][v] == self.core_states[core2].PTE()
    }

    pub open spec fn shootdown_exists(self, c: Constants) -> bool {
       self.os_ext.shootdown_vec.open_requests !== set![]
           ==> {
               &&& self.os_ext.lock matches Some(core)
               &&& self.core_states[core] is UnmapShootdownWaiting
           }
    }

    pub open spec fn tlb_inv(self, c: Constants) -> bool {
        &&& self.inv_tlb_wf(c)
        &&& self.inv_shootdown_wf(c)
        &&& self.shootdown_exists(c)
        &&& self.shootdown_cores_valid(c)
        &&& self.successful_invlpg(c)
        &&& self.successful_IPI(c)
        &&& self.TLB_dom_subset_of_pt_and_inflight_unmap_vaddr(c)
        &&& self.TLB_interp_pt_mem_agree(c)
        &&& self.TLB_unmap_agree(c)
        &&& self.pending_unmap_is_unmap_vaddr(c)
        &&& self.all_cores_nonpos_before_shootdown(c)
    }

    pub open spec fn pending_unmap_is_unmap_vaddr(self, c: Constants) -> bool {
        forall|va| #[trigger] self.mmu@.pending_unmaps.contains_key(va)
                ==> {
                    &&& self.is_unmap_vaddr_core(self.os_ext.lock->Some_0, va as nat)
                    &&& self.mmu@.pending_unmaps[va] == self.core_states[self.os_ext.lock->Some_0].PTE()
                }
    }

}
}



// File: spec_t/os_ext.rs
pub mod os_ext {
    use vstd::prelude::*;
    use crate::defs::*;

// describes how the rest of the OS behaves
// This is the "rest of the OS". It specifies the kernel lock, (de-)allocation, and
// shootdown coordination

pub struct State {
    pub lock: Option<Core>,
    pub shootdown_vec: ShootdownVector,
    pub allocated: Set<MemRegion>,
}

pub struct ShootdownVector {
    pub vaddr: nat,
    pub open_requests: Set<Core>,
}

pub open spec fn init(pre: State, c: crate::Constants) -> bool {
    &&& pre.lock === None
    &&& pre.shootdown_vec.open_requests === set![]
    &&& c.memories_disjoint()
    // The OS state machine specifies this field. We assume that we already start with one
    // directory allocated for the PML4 directory.
    //&&& pre.allocated === set![]
}
}


// File: spec_t/mmu/mod.rs
// trusted: definitions for the trusted low-level hardware model

// Only used in the simplified hardware models.

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

/// Each refinement layer uses the same set of constants.
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

    pub open spec fn in_ptmem_range(self, addr: nat, size: nat) -> bool {
        &&& self.range_ptmem.0 <= addr
        &&& addr + size <= self.range_ptmem.1
    }

    pub open spec fn memories_disjoint(self) -> bool {
        &&& self.range_mem.0 < self.range_mem.1 < self.range_ptmem.0 < self.range_ptmem.1
        &&& self.range_ptmem.1 <= crate::defs::MAX_PHYADDR
    }

}

// File: spec_t/os_invariant.rs
pub proof fn init_implies_tlb_inv(c: os::Constants, s: os::State)
    requires os::init(c, s),
    ensures s.tlb_inv(c),
{
}

}
