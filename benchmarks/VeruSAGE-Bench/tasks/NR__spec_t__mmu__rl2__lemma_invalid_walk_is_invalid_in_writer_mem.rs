use vstd::prelude::*;

fn main() {}

verus!{

global size_of usize == 8;

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

// layer:
// 0 -> PML4
// 1 -> PDPT, Page Directory Pointer Table
// 2 -> PD, Page Directory
// 3 -> PT, Page Table
// MASK_FLAG_* are flags valid for entries at all levels.
pub const MASK_FLAG_P: usize = bit!(0usize);

pub const MASK_FLAG_RW: usize = bit!(1usize);

pub const MASK_FLAG_US: usize = bit!(2usize);

pub const MASK_FLAG_PWT: usize = bit!(3usize);

pub const MASK_FLAG_PCD: usize = bit!(4usize);

pub const MASK_FLAG_XD: usize = bit!(63usize);

// MASK_PG_FLAG_* are flags valid for all page mapping entries, unless a specialized version for that
// layer exists, e.g. for layer 3 MASK_L3_PG_FLAG_PAT is used rather than MASK_PG_FLAG_PAT.

pub const MASK_PG_FLAG_G: usize = bit!(8usize);

pub const MASK_PG_FLAG_PAT: usize = bit!(12usize);

pub const MASK_L1_PG_FLAG_PS: usize = bit!(7usize);

pub const MASK_L2_PG_FLAG_PS: usize = bit!(7usize);

pub const MASK_L3_PG_FLAG_PAT: usize = bit!(7usize);

pub const MASK_DIRTY_ACCESS: usize = bit!(5) | bit!(6);
pub const MASK_NEG_DIRTY_ACCESS: usize = !MASK_DIRTY_ACCESS;

// In the implementation we can always use the 12:52 mask as the invariant guarantees that in the
// other cases, the lower bits are already zero anyway.
// We cannot use dual exec/spec constants here because for those Verus currently doesn't support
// manually guiding the no-overflow proofs.
pub spec const MASK_ADDR_SPEC: usize = bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_ADDR_SPEC)]
pub exec const MASK_ADDR: usize ensures MASK_ADDR == MASK_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L1_PG_ADDR_SPEC: usize = bitmask_inc!(30usize, MAX_PHYADDR_WIDTH - 1);
#[verifier::when_used_as_spec(MASK_L1_PG_ADDR_SPEC)]
pub exec const MASK_L1_PG_ADDR: usize ensures MASK_L1_PG_ADDR == MASK_L1_PG_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(30usize, MAX_PHYADDR_WIDTH - 1)
}


pub spec const MASK_L2_PG_ADDR_SPEC: usize = bitmask_inc!(21usize, MAX_PHYADDR_WIDTH - 1);
#[verifier::when_used_as_spec(MASK_L2_PG_ADDR_SPEC)]
pub exec const MASK_L2_PG_ADDR: usize ensures MASK_L2_PG_ADDR == MASK_L2_PG_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(21usize, MAX_PHYADDR_WIDTH - 1)
}

pub spec const MASK_L3_PG_ADDR_SPEC: usize = bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1);

#[verifier::when_used_as_spec(MASK_L3_PG_ADDR_SPEC)]
pub exec const MASK_L3_PG_ADDR: usize ensures MASK_L3_PG_ADDR == MASK_L3_PG_ADDR_SPEC {
    proof {
        axiom_max_phyaddr_width_facts();
    }
    bitmask_inc!(12usize, MAX_PHYADDR_WIDTH - 1)
}

#[allow(unused_macros)]
macro_rules! l0_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(39usize,47usize)) >> 39usize }
}

pub(crate) use l0_bits;

#[allow(unused_macros)]
macro_rules! l1_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(30usize,38usize)) >> 30usize }
}

pub(crate) use l1_bits;

#[allow(unused_macros)]
macro_rules! l2_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(21usize,29usize)) >> 21usize }
}

pub(crate) use l2_bits;

#[allow(unused_macros)]
macro_rules! l3_bits {
    ($addr:expr) => { ($addr & bitmask_inc!(12usize,20usize)) >> 12usize }
}

pub(crate) use l3_bits;


#[repr(transparent)]
#[allow(repr_transparent_external_private_fields)]
// An entry in any page directory (i.e. in PML4, PDPT, PD or PT)
pub struct PDE {
    pub entry: usize,
    pub layer: Ghost<nat>,
}

// This impl defines everything necessary for the page table walk semantics.
// PDE is reused in the implementation, which has an additional impl block for it in
// `impl_u::l2_impl`.
impl PDE {

    pub open spec fn view(self) -> GPDE {
        let v = self.entry;
        let P   = v & MASK_FLAG_P    == MASK_FLAG_P;
        let RW  = v & MASK_FLAG_RW   == MASK_FLAG_RW;
        let US  = v & MASK_FLAG_US   == MASK_FLAG_US;
        let PWT = v & MASK_FLAG_PWT  == MASK_FLAG_PWT;
        let PCD = v & MASK_FLAG_PCD  == MASK_FLAG_PCD;
        let XD  = v & MASK_FLAG_XD   == MASK_FLAG_XD;
        let G   = v & MASK_PG_FLAG_G == MASK_PG_FLAG_G;
        if v & MASK_FLAG_P == MASK_FLAG_P && self.all_mb0_bits_are_zero() {
            if self.layer == 0 {
                let addr = v & MASK_ADDR;
                GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
            } else if self.layer == 1 {
                if v & MASK_L1_PG_FLAG_PS == MASK_L1_PG_FLAG_PS {
                    // super page mapping
                    let addr = v & MASK_L1_PG_ADDR;
                    let PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
                    GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
                } else {
                    let addr = v & MASK_ADDR;
                    GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
                }
            } else if self.layer == 2 {
                if v & MASK_L2_PG_FLAG_PS == MASK_L2_PG_FLAG_PS {
                    // huge page mapping
                    let addr = v & MASK_L2_PG_ADDR;
                    let PAT = v & MASK_PG_FLAG_PAT == MASK_PG_FLAG_PAT;
                    GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
                } else {
                    let addr = v & MASK_ADDR;
                    GPDE::Directory { addr, P, RW, US, PWT, PCD, XD }
                }
            } else if self.layer == 3 {
                let addr = v & MASK_L3_PG_ADDR;
                let PAT = v & MASK_L3_PG_FLAG_PAT == MASK_L3_PG_FLAG_PAT;
                GPDE::Page { addr, P, RW, US, PWT, PCD, G, PAT, XD }
            } else {
                arbitrary()
            }
        } else {
            GPDE::Invalid
        }
    }

	#[verifier::external_body]
    pub open spec fn all_mb0_bits_are_zero(self) -> bool {
		unimplemented!()
	}


}

impl Flags {

    pub open spec fn from_GPDE(pde: GPDE) -> Flags
        recommends !(pde is Invalid)
    {
        match pde {
            GPDE::Directory { RW, US, XD, .. } =>
                Flags::from_bits(RW, US, XD),
            GPDE::Page { RW, US, XD, .. } =>
                Flags::from_bits(RW, US, XD),
            _ => arbitrary(),
        }
    }

}

// File: spec_t/mmu/defs.rs
macro_rules! bitmask_inc {
    ($low:expr,$high:expr) => {
        (!(!0usize << (($high+1usize)-$low))) << $low
    }
}

pub(crate) use bitmask_inc;

macro_rules! bit {
    ($v:expr) => {
        1usize << $v
    }
}

pub(crate) use bit;

// The maximum physical address width is between 32 and 52 bits.
#[verifier(external_body)]
pub const MAX_PHYADDR_WIDTH: usize = 52;

pub axiom fn axiom_max_phyaddr_width_facts()
    ensures
        32 <= MAX_PHYADDR_WIDTH <= 52,
;
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


pub const WORD_SIZE: usize = 8;

pub const PAGE_SIZE: usize = 4096;

pub const L3_ENTRY_SIZE: usize = PAGE_SIZE;

pub const L2_ENTRY_SIZE: usize = 512 * L3_ENTRY_SIZE;

pub const L1_ENTRY_SIZE: usize = 512 * L2_ENTRY_SIZE;

pub open spec(checked) fn align_to_usize(a: usize, b: usize) -> usize {
    sub(a, a % b)
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

impl Flags {

    pub open spec fn from_bits(flag_RW: bool, flag_US: bool, flag_XD: bool) -> Flags {
        Flags {
            is_writable: flag_RW,
            is_supervisor: !flag_US,
            disable_execute: flag_XD,
        }
    }

    pub open spec fn combine(self, other: Flags) -> Flags {
        Flags {
            is_writable: self.is_writable && other.is_writable,
            is_supervisor: self.is_supervisor || other.is_supervisor,
            disable_execute: self.disable_execute || other.disable_execute,
        }
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

pub enum WalkResult {
    Valid { vbase: usize, pte: PTE },
    /// A `WalkResult::Invalid` indicates that no valid translation exists for the given (8-aligned) vaddr
    Invalid { vaddr: usize },
}

impl Walk {

    pub open spec fn result(self) -> WalkResult {
        let path = self.path;
        if path.last().1 is Page {
            let (vbase, base, size) = if path.len() == 2 {
                (align_to_usize(self.vaddr, L1_ENTRY_SIZE), path[1].1->Page_addr, L1_ENTRY_SIZE)
            } else if path.len() == 3 {
                (align_to_usize(self.vaddr, L2_ENTRY_SIZE), path[2].1->Page_addr, L2_ENTRY_SIZE)
            } else if path.len() == 4 {
                (align_to_usize(self.vaddr, L3_ENTRY_SIZE), path[3].1->Page_addr, L3_ENTRY_SIZE)
            } else { arbitrary() };
            WalkResult::Valid {
                vbase,
                pte: PTE {
                    frame: MemRegion { base: base as nat, size: size as nat },
                    flags: self.flags(),
                }
            }
        } else if path.last().1 is Invalid {
            // The result holds for one page
            WalkResult::Invalid { vaddr: align_to_usize(self.vaddr, PAGE_SIZE) }
        } else {
            arbitrary()
        }
    }

    pub open spec fn flags(self) -> Flags {
        let path = self.path;
        let flags0 = Flags::from_GPDE(path[0].1);
        let flags1 = flags0.combine(Flags::from_GPDE(path[1].1));
        let flags2 = flags1.combine(Flags::from_GPDE(path[2].1));
        let flags3 = flags2.combine(Flags::from_GPDE(path[3].1));
        if path.len() == 1 {
            flags0
        } else if path.len() == 2 {
            flags1
        } else if path.len() == 3 {
            flags2
        } else if path.len() == 4 {
            flags3
        } else { arbitrary() }
    }

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
        &&& self.range_ptmem.1 <= MAX_PHYADDR
    }

}


pub trait SeqTupExt: Sized {
    type A;
    spec fn contains_fst(self, fst: Self::A) -> bool;

}


impl<A,B> SeqTupExt for Seq<(A, B)> {
    type A = A;

    open spec fn contains_fst(self, fst: Self::A) -> bool {
        exists|i| 0 <= i < self.len() && #[trigger] self[i] == (fst, self[i].1)
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

    pub open spec fn pt_walk(self, vaddr: usize) -> Walk {
        let l0_idx = mul(l0_bits!(vaddr), WORD_SIZE);
        let l1_idx = mul(l1_bits!(vaddr), WORD_SIZE);
        let l2_idx = mul(l2_bits!(vaddr), WORD_SIZE);
        let l3_idx = mul(l3_bits!(vaddr), WORD_SIZE);
        let l0_addr = add(self.pml4, l0_idx);
        let l0e = PDE { entry: self.read(l0_addr), layer: Ghost(0) };
        match l0e@ {
            GPDE::Directory { addr: l1_daddr, .. } => {
                let l1_addr = add(l1_daddr, l1_idx);
                let l1e = PDE { entry: self.read(l1_addr), layer: Ghost(1) };
                match l1e@ {
                    GPDE::Directory { addr: l2_daddr, .. } => {
                        let l2_addr = add(l2_daddr, l2_idx);
                        let l2e = PDE { entry: self.read(l2_addr), layer: Ghost(2) };
                        match l2e@ {
                            GPDE::Directory { addr: l3_daddr, .. } => {
                                let l3_addr = add(l3_daddr, l3_idx);
                                let l3e = PDE { entry: self.read(l3_addr), layer: Ghost(3) };
                                Walk {
                                    vaddr,
                                    path: seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@), (l3_addr, l3e@)],
                                    complete: true,
                                }
                            },
                            _ => {
                                Walk {
                                    vaddr,
                                    path: seq![(l0_addr, l0e@), (l1_addr, l1e@), (l2_addr, l2e@)],
                                    complete: true,
                                }
                            },
                        }
                    },
                    _ => {
                        Walk { vaddr, path: seq![(l0_addr, l0e@), (l1_addr, l1e@)], complete: true }
                    },
                }
            },
            _ => {
                Walk { vaddr, path: seq![(l0_addr, l0e@)], complete: true }
            },
        }
    }

}

// File: spec_t/mmu/rl3.rs
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


// File: spec_t/mmu/rl2.rs
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

    #[verifier(inline)]
    pub open spec fn writer_sbuf(self) -> Seq<(usize, usize)> {
        self.sbuf[self.writes.core]
    }

    pub open spec fn core_mem(self, core: Core) -> PTMem {
        self.pt_mem.write_seq(self.sbuf[core])
    }

    #[verifier(inline)]
    pub open spec fn writer_mem(self) -> PTMem {
        self.core_mem(self.writes.core)
    }

}


impl State {

    pub open spec fn wf(self, c: Constants) -> bool {
        &&& c.valid_core(self.writes.core)
        &&& self.writes.tso.finite()
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.walks.contains_key(core)
        &&& forall|core| #[trigger] c.valid_core(core) <==> self.sbuf.contains_key(core)
        &&& forall|core| #[trigger] self.walks.contains_key(core) ==> self.walks[core].finite()

        &&& aligned(self.pt_mem.pml4 as nat, 4096)
        &&& c.in_ptmem_range(self.pt_mem.pml4 as nat, 4096)
        &&& c.memories_disjoint()
        //&&& self.phys_mem.len() == c.range_mem.1
        &&& self.wf_ptmem_range(c)
    }

	#[verifier::external_body]
    pub open spec fn wf_ptmem_range(self, c: Constants) -> bool {
		unimplemented!()
	}


    #[verifier(opaque)]
    pub open spec fn inv_unmapping__core_vs_writer_reads(self, c: Constants) -> bool {
        forall|core, addr|
            #![trigger self.core_mem(core).read(addr)]
            #![trigger c.valid_core(core), self.writer_sbuf().contains_fst(addr)]
            c.valid_core(core) ==>
            (if self.core_mem(core).read(addr) & 1 == 0 {
                &&& (self.writer_sbuf().contains_fst(addr) ==> core == self.writes.core)
                &&& self.writer_mem().read(addr) == self.core_mem(core).read(addr)
            } else {
                ||| self.writer_mem().read(addr) == self.core_mem(core).read(addr)
                ||| self.writer_mem().read(addr) & 1 == 0
            })
    }

}

	#[verifier::external_body]
broadcast proof fn lemma_core_mem_pml4(state: State, c: Constants, core: Core)
    requires
        #[trigger] c.valid_core(core),
    ensures
        (#[trigger] state.core_mem(core)).pml4 == state.pt_mem.pml4,
	{
		unimplemented!()
	}



broadcast proof fn lemma_invalid_walk_is_invalid_in_writer_mem(pre: State, c: Constants, core: Core, va: usize)
    requires
        pre.wf(c),
        pre.inv_unmapping__core_vs_writer_reads(c),
        #[trigger] c.valid_core(core),
        pre.core_mem(core).pt_walk(va).result() is Invalid,
    ensures
        #[trigger] pre.writer_mem().pt_walk(va).result() is Invalid,
{
}



}
