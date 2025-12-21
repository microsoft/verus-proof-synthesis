use vstd::prelude::*;
use crate::defs::*;

fn main() {}

verus!{

global size_of usize == 8;

// File: spec_t/mmu/rl1.rs
pub mod rl1{
use vstd::prelude::*;
use crate::defs::*;
use crate::{PTE, PTMem, Polarity};
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
}

// File: spec_t/mmu/rl2.rs
pub mod rl2{
    use vstd::prelude::*;
    use crate::{PTE, PTMem, Polarity, Walk};
    use crate::defs::*;
    use crate::rl3::Writes;

// This mod contains refinement layer 2 of the MMU. Compared to layer 3, it expresses translation
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
use crate::{PTMem, Walk, Polarity};

// This mod contains refinement layer 3 of the MMU. This is the most concrete MMU model, i.e. the
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

pub struct History {
    pub happy: bool,
    /// All partial walks since the last invlpg
    pub walks: Map<Core, Set<Walk>>,
    pub writes: Writes,
    pub pending_maps: Map<usize, PTE>,
    pub pending_unmaps: Map<usize, PTE>,
    pub polarity: Polarity,
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

pub open spec fn between(x: nat, a: nat, b: nat) -> bool {
    a <= x && x < b
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

// File: spec_t/hlspec.rs
pub mod hlspec{
use vstd::prelude::*;
use crate::{PTE};
use crate::defs::MAX_BASE;

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

pub open spec fn init(c: Constants, s: State) -> bool {
    &&& s.mem.len() === MAX_BASE
    &&& s.mappings === Map::empty()
    &&& forall|id: nat| id < c.thread_no ==> (s.thread_state[id] === ThreadState::Idle)
    &&& wf(c, s)
    &&& s.sound
}
}

// File: spec_t/os.rs
pub mod os {
use vstd::prelude::*;
use crate::defs::*;

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

impl Constants {

    pub open spec fn interp(self) -> crate::hlspec::Constants {
        crate::hlspec::Constants { thread_no: self.ult_no, phys_mem_size: self.common.phys_mem_size }
    }

}


impl State {

    pub open spec fn interp_pt_mem(self) -> Map<nat, PTE> {
        nat_keys(self.mmu@.pt_mem@)
    }

    pub open spec fn inflight_vaddr(self) -> Set<nat> {
        Set::new(|v_address: nat| {
            &&& self.interp_pt_mem().contains_key(v_address)
            &&& exists|core: Core|
                self.core_states.contains_key(core) && match self.core_states[core] {
                    CoreState::UnmapWaiting { ult_id, vaddr }
                    | CoreState::UnmapExecuting { ult_id, vaddr, .. }
                    | CoreState::UnmapOpDone { ult_id, vaddr, .. }
                    | CoreState::UnmapShootdownWaiting { ult_id, vaddr, .. }
                    | CoreState::MapDone {ult_id, vaddr, result: Ok(()), .. } => {
                        vaddr === v_address
                    },
                    _ => false,
                }
        })
    }

    pub open spec fn effective_mappings(self) -> Map<nat, PTE> {
        self.interp_pt_mem().remove_keys(self.inflight_vaddr())
    }

    pub open spec fn has_base_and_pte_for_vaddr(applied_mappings: Map<nat, PTE>, vaddr: int) -> bool {
        exists|base: nat, pte: PTE| #![auto]
            applied_mappings.contains_pair(base, pte)
            && between(vaddr as nat, base, base + pte.frame.size)
    }

    pub open spec fn base_and_pte_for_vaddr(applied_mappings: Map<nat, PTE>, vaddr: int) -> (nat, PTE) {
        choose|base: nat, pte: PTE| #![auto]
            applied_mappings.contains_pair(base, pte)
            && between(vaddr as nat, base, base + pte.frame.size)
    }

    pub open spec fn vmem_apply_mappings(
        applied_mappings: Map<nat, PTE>,
        phys_mem: Seq<u8>
    ) -> Seq<u8> {
        Seq::new(
            MAX_BASE,
            |vaddr: int| {
                if Self::has_base_and_pte_for_vaddr(applied_mappings, vaddr) {
                    let (base, pte) = Self::base_and_pte_for_vaddr(applied_mappings, vaddr);
                    phys_mem[pte.frame.base + (vaddr - base)]
                } else {
                    0
                }
        })
    }

    pub open spec fn applied_mappings(self) -> Map<nat, PTE> {
        // Prefer interp_pt_mem because there might be a situation where we have
        // something in the MapStart state which conflicts with something in interp_pt_mem.
        // In that case the map will eventually end in an error;
        // we want to use the mapping from interp_pt_mem instead.
        self.extra_mappings()
            .union_prefer_right(self.interp_pt_mem())
    }

    pub open spec fn interp_vmem(self, c: Constants) -> Seq<u8> {
        Self::vmem_apply_mappings(self.applied_mappings(), self.mmu@.phys_mem)
    }

	#[verifier::external_body]
    pub open spec fn extra_mappings(self) -> Map<nat, PTE> {
		unimplemented!()
	}


    pub open spec fn interp_thread_state(self, c: Constants) -> Map<nat, crate::hlspec::ThreadState> {
        Map::new(
            |ult_id: nat| c.valid_ult(ult_id),
            |ult_id: nat| {
                    match self.core_states[c.ult2core[ult_id]] {
                        CoreState::MapWaiting { ult_id: ult_id2, vaddr, pte }
                        | CoreState::MapExecuting { ult_id: ult_id2, vaddr, pte }
                        | CoreState::MapDone { ult_id: ult_id2, vaddr, pte, .. } => {
                            if ult_id2 == ult_id {
                                crate::hlspec::ThreadState::Map { vaddr, pte }
                            } else {
                                crate::hlspec::ThreadState::Idle
                            }
                        },
                        CoreState::UnmapWaiting { ult_id: ult_id2, vaddr }
                        | CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: None } => {
                            let pte = if self.interp_pt_mem().contains_key(vaddr) {
                                Some(self.interp_pt_mem()[vaddr])
                            } else {
                                None
                            };
                            if ult_id2 == ult_id {
                                crate::hlspec::ThreadState::Unmap { vaddr, pte }
                            } else {
                                crate::hlspec::ThreadState::Idle
                            }
                        },
                        CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: Some(result) }
                        | CoreState::UnmapOpDone { ult_id: ult_id2, vaddr, result }
                        | CoreState::UnmapShootdownWaiting { ult_id: ult_id2, vaddr, result } => {
                            if ult_id2 == ult_id {
                                crate::hlspec::ThreadState::Unmap { vaddr, pte:
                                    match result {
                                        Ok(pte) => Some(pte),
                                        Err(_) => None,
                                    }
                                }
                            } else {
                                crate::hlspec::ThreadState::Idle
                            }
                        },
                        CoreState::Idle => crate::hlspec::ThreadState::Idle,
                    }
                },
        )
    }

    pub open spec fn interp(self, c: Constants) -> crate::hlspec::State {
        let mappings = self.effective_mappings();
        let mem = self.interp_vmem(c);
        let thread_state = self.interp_thread_state(c);
        let sound = self.sound;
        crate::hlspec::State { mem, mappings, thread_state, sound }
    }

}
}


// File: spec_t/os_ext.rs
pub mod os_ext {
use vstd::prelude::*;
use crate::defs::*;

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


    pub open spec fn memories_disjoint(self) -> bool {
        &&& self.range_mem.0 < self.range_mem.1 < self.range_ptmem.0 < self.range_ptmem.1
        &&& self.range_ptmem.1 <= MAX_PHYADDR
    }

}

// File: impl_u/os_refinement.rs
pub proof fn os_init_refines_hl_init(c: crate::os::Constants, s: crate::os::State)
    requires
        crate::os::init(c, s),
    ensures
        crate::hlspec::init(c.interp(), s.interp(c)),
{
}
}
