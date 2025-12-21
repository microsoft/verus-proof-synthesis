use vstd::prelude::*;
use crate::defs::*;

fn main() {}

verus!{
global size_of usize == 8;

pub mod rl1 {
use vstd::prelude::*;
use crate::defs::*;
use crate::{PTE, PTMem, Polarity};
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
    pub polarity: Polarity,
}
}

pub mod rl2{
use vstd::prelude::*;
use crate::{PTE, PTMem, Polarity, Walk};
use crate::defs::*;
use crate::rl3::Writes;

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

pub mod rl3 {
use vstd::prelude::*;
use crate::defs::*;
use crate::{PTMem, Walk, Polarity};

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

    pub mod to_rl1 {

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

pub mod defs {
use vstd::prelude::*;

// File: spec_t/mmu/defs.rs
pub const X86_NUM_ENTRIES: usize = 512;

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

impl State {

    pub open spec fn interp_pt_mem(self) -> Map<nat, PTE> {
        crate::defs::nat_keys(self.mmu@.pt_mem@)
    }

    pub open spec fn has_base_and_pte_for_vaddr(applied_mappings: Map<nat, PTE>, vaddr: int) -> bool {
        exists|base: nat, pte: PTE| #![auto]
            applied_mappings.contains_pair(base, pte)
            && crate::defs::between(vaddr as nat, base, base + pte.frame.size)
    }

    pub open spec fn base_and_pte_for_vaddr(applied_mappings: Map<nat, PTE>, vaddr: int) -> (nat, PTE) {
        choose|base: nat, pte: PTE| #![auto]
            applied_mappings.contains_pair(base, pte)
            && crate::defs::between(vaddr as nat, base, base + pte.frame.size)
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


// File: impl_u/os_refinement.rs
spec fn no_overlaps(m: Map<nat, PTE>) -> bool {
    forall |i, j|
        #[trigger] m.dom().contains(i) && #[trigger] m.dom().contains(j) && i != j
          ==> i + m[i].frame.size <= j
           || j + m[j].frame.size <= i
}

proof fn interp_vmem_subrange(c: os::Constants, s: os::State, base: nat, pte: PTE, vaddr: int, size: int)
    requires
        no_overlaps(s.applied_mappings()),
        s.applied_mappings().dom().contains(base),
        s.applied_mappings()[base] == pte,
        base <= vaddr,
        size >= 0,
        vaddr + size <= base + pte.frame.size,

        base + pte.frame.size <= s.interp_vmem(c).len(),
        pte.frame.base + pte.frame.size <= s.mmu@.phys_mem.len(),

    ensures ({
        let paddr = pte.frame.base + vaddr - base;
        s.interp_vmem(c).subrange(vaddr, vaddr + size)
            == s.mmu@.phys_mem.subrange(paddr, paddr + size)
    })
{
    let paddr = pte.frame.base + vaddr - base;

    vstd::seq_lib::assert_seqs_equal!(
        s.interp_vmem(c).subrange(vaddr, vaddr + size),
        s.mmu@.phys_mem.subrange(paddr, paddr + size),
        idx => {
            let v = vaddr + idx;
            let p = paddr + idx;

            let (base0, pte0) = os::State::base_and_pte_for_vaddr(s.applied_mappings(), vaddr);

            assert(s.applied_mappings().contains_pair(base, pte));
            assert(crate::defs::between(v as nat, base, base + pte.frame.size));

            assert(s.applied_mappings().contains_pair(base0, pte0)
              && crate::defs::between(v as nat, base0, base0 + pte0.frame.size));

            assert(base0 == base);
            assert(pte0 == pte);

            assert(s.interp_vmem(c)[v] == s.mmu@.phys_mem[p]);
        }
    );
}


}
