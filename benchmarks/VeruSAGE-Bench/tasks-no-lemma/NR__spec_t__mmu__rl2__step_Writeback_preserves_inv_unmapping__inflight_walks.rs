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
pub const X86_NUM_ENTRIES: usize = 512;

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

pub spec const X86_MAX_ENTRY_SIZE: nat = 512 * 512 * 512 * 4096;

pub spec const MAX_BASE: nat = X86_MAX_ENTRY_SIZE * (X86_NUM_ENTRIES as nat);

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


pub open spec fn update_range<A>(s: Seq<A>, idx: int, new: Seq<A>) -> Seq<A>
{
    s.subrange(0, idx)
      + new
      + s.subrange(idx + new.len(), s.len() as int)
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

impl WalkResult {

    pub open spec fn vaddr(self) -> usize {
        match self {
            WalkResult::Valid { vbase, .. } => vbase,
            WalkResult::Invalid { vaddr, .. } => vaddr,
        }
    }

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


pub enum Lbl {
    /// Internal event
    Tau,
    /// Memory operation on non-page-table memory
    /// Core, virtual address, memory operation
    MemOp(Core, usize, MemOp),
    /// Write to page table memory.
    /// Core, physical address, written value
    Write(Core, usize, usize),
    /// Read from page table memory.
    /// Core, physical address, read value
    Read(Core, usize, usize),
    /// Invlpg instruction
    /// Core and virtual address
    Invlpg(Core, usize),
    /// Serializing instruction
    Barrier(Core),
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

    pub open spec fn is_nonneg_write(self, addr: usize, value: usize) -> bool {
        &&& self.read(addr) & 1 == 0
        &&& value & 1 == 1
    }

    pub open spec fn is_nonpos_write(self, addr: usize, value: usize) -> bool {
        &&& self.read(addr) & 1 == 1
        &&& value & 1 == 0
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

	#[verifier::external_body]
    pub open spec fn view(self) -> Map<usize,PTE> {
		unimplemented!()
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

pub enum Step {
    Invlpg,
    // Faulting memory op due to failed translation
    MemOpNoTr { walk: Walk },
    // Memory op using a translation from the TLB
    MemOpTLB { tlb_va: usize },
    // Non-atomic page table walks
    WalkInit { core: Core, vaddr: usize },
    WalkStep { core: Core, walk: Walk },
    TLBFill { core: Core, walk: Walk },
    TLBEvict { core: Core, tlb_va: usize },
    // TSO
    WriteNonneg,
    WriteNonpos,
    Writeback { core: Core },
    Read,
    Barrier,
    SadWrite,
    Sadness,
    Stutter,
}

impl State {

    pub open spec fn read_from_mem_tso(self, core: Core, addr: usize) -> usize {
        self.core_mem(core).read(addr)
    }

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

    pub open spec fn is_happy_writenonneg(self, core: Core, addr: usize, value: usize) -> bool {
        &&& !self.writes.tso.is_empty() ==> core == self.writes.core
        &&& self.writer_mem().is_nonneg_write(addr, value)
    }

    pub open spec fn is_happy_writenonpos(self, core: Core, addr: usize, value: usize) -> bool {
        &&& !self.writes.tso.is_empty() ==> core == self.writes.core
        &&& self.writer_mem().is_nonpos_write(addr, value)
    }

    pub open spec fn can_flip_polarity(self, c: Constants) -> bool {
        //&&& self.hist.pending_maps === map![]
        //&&& self.hist.pending_unmaps === map![]
        &&& self.writes.tso === set![]
        &&& self.writes.nonpos === set![]
    }

}


pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)
    &&& pre.happy

    &&& c.valid_core(core)
    // Invlpg is a serializing instruction
    &&& pre.sbuf[core].len() == 0
    &&& !pre.tlbs[core].contains_key(va)

    &&& post == State {
        walks: pre.walks.insert(core, set![]),
        writes: Writes {
            core: pre.writes.core,
            tso: if core == pre.writes.core { set![] } else { pre.writes.tso },
            nonpos:
                if post.writes.tso === set![] {
                    pre.writes.nonpos.remove(core)
                } else { pre.writes.nonpos },
        },
        hist: History {
            pending_maps: if core == pre.writes.core { map![] } else { pre.hist.pending_maps },
            pending_unmaps: if post.writes.nonpos === set![] { map![] } else { pre.hist.pending_unmaps },
            ..pre.hist
        },
        ..pre
    }
}

pub open spec fn step_MemOpNoTr(
    pre: State,
    post: State,
    c: Constants,
    walk: Walk,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy

    &&& {
    let walk_next = walk_next(pre.core_mem(core), walk);
    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.walks[core].contains(walk)
    &&& walk.vaddr == memop_vaddr
    &&& walk_next.complete
    &&& walk_next.result() is Invalid
    &&& memop.is_pagefault()
    }

    &&& post == pre
}

pub open spec fn step_MemOpTLB(
    pre: State,
    post: State,
    c: Constants,
    tlb_va: usize,
    lbl: Lbl,
) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.tlbs[core].contains_key(tlb_va)
    &&& {
    let pte = pre.tlbs[core][tlb_va];
    let paddr = pte.frame.base + (memop_vaddr - tlb_va);
    &&& tlb_va <= memop_vaddr < tlb_va + pte.frame.size
    &&& match memop {
        MemOp::Store { new_value, result } => {
            if paddr < c.phys_mem_size && !pte.flags.is_supervisor && pte.flags.is_writable {
                &&& result is Ok
                &&& post.phys_mem === update_range(pre.phys_mem, paddr, new_value)
            } else {
                &&& result is Pagefault
                &&& post.phys_mem === pre.phys_mem
            }
        },
        MemOp::Load { is_exec, result, .. } => {
            if paddr < c.phys_mem_size && !pte.flags.is_supervisor && (is_exec ==> !pte.flags.disable_execute) {
                &&& result == LoadResult::Value(pre.phys_mem.subrange(paddr, paddr + memop.op_size()))
                &&& post.phys_mem === pre.phys_mem
            } else {
                &&& result is Pagefault
                &&& post.phys_mem === pre.phys_mem
            }
        },
    }
    }

    &&& post.happy == pre.happy
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.walks == pre.walks
    &&& post.sbuf == pre.sbuf
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
    &&& post.hist == pre.hist
}

pub open spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    let walk = Walk { vaddr, path: seq![], complete: false };
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& aligned(vaddr as nat, 8)
    &&& vaddr < MAX_BASE

    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk))
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
    &&& post.hist.pending_maps == pre.hist.pending_maps
    &&& post.hist.pending_unmaps == pre.hist.pending_unmaps
}

pub open spec fn step_WalkStep(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    lbl: Lbl
    ) -> bool
{
    let walk_next = walk_next(pre.core_mem(core), walk);
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& !walk_next.complete

    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf
    &&& post.walks == pre.walks.insert(core, pre.walks[core].insert(walk_next))
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
    &&& post.hist.pending_maps == pre.hist.pending_maps
    &&& post.hist.pending_unmaps == pre.hist.pending_unmaps
}

pub open spec fn step_TLBFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
    let walk_next = walk_next(pre.core_mem(core), walk);
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.walks[core].contains(walk)
    &&& walk_next.complete
    &&& walk_next.result() matches WalkResult::Valid { vbase, pte }

    &&& post == State {
        tlbs: pre.tlbs.insert(core, pre.tlbs[core].insert(vbase, pte)),
        ..pre
    }
}

pub open spec fn step_TLBEvict(pre: State, post: State, c: Constants, core: Core, tlb_va: usize, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.tlbs[core].contains_key(tlb_va)

    &&& post == State {
        tlbs: pre.tlbs.insert(core, pre.tlbs[core].remove(tlb_va)),
        ..pre
    }
}

pub open spec fn step_WriteNonneg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.is_happy_writenonneg(core, addr, value)
    &&& pre.polarity is Mapping || pre.can_flip_polarity(c)

    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.walks == pre.walks
    &&& post.writes.tso === pre.writes.tso.insert(addr)
    &&& post.writes.nonpos === pre.writes.nonpos
    &&& post.writes.core == core
    &&& post.polarity == Polarity::Mapping
    &&& post.hist.pending_maps == pre.hist.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.writer_mem()@.contains_key(vbase) && !pre.writer_mem()@.contains_key(vbase),
            |vbase| post.writer_mem()@[vbase]
        ))
    &&& post.hist.pending_unmaps == pre.hist.pending_unmaps
}

pub open spec fn step_WriteNonpos(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& aligned(addr as nat, 8)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& pre.is_happy_writenonpos(core, addr, value)
    &&& pre.polarity is Unmapping || pre.can_flip_polarity(c)

    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].push((addr, value)))
    &&& post.walks == pre.walks
    &&& post.writes.tso === pre.writes.tso.insert(addr)
    &&& post.writes.nonpos == Set::new(|core| c.valid_core(core))
    &&& post.writes.core == core
    &&& post.polarity == Polarity::Unmapping
    &&& post.hist.pending_maps == pre.hist.pending_maps
    &&& post.hist.pending_unmaps == pre.hist.pending_unmaps.union_prefer_right(
        Map::new(
            |vbase| pre.writer_mem()@.contains_key(vbase) && !post.writer_mem()@.contains_key(vbase),
            |vbase| pre.writer_mem()@[vbase]
        ))
}

pub open spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
    let (addr, value) = pre.sbuf[core][0];
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& 0 < pre.sbuf[core].len()

    &&& post.happy == pre.happy
    &&& post.phys_mem == pre.phys_mem
    &&& post.pt_mem == pre.pt_mem.write(addr, value)
    &&& post.tlbs == pre.tlbs
    &&& post.sbuf == pre.sbuf.insert(core, pre.sbuf[core].drop_first())
    &&& post.walks == pre.walks
    &&& post.writes == pre.writes
    &&& post.polarity == pre.polarity
    &&& post.hist.pending_maps == pre.hist.pending_maps
    &&& post.hist.pending_unmaps == pre.hist.pending_unmaps
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& value & MASK_NEG_DIRTY_ACCESS == pre.read_from_mem_tso(core, addr) & MASK_NEG_DIRTY_ACCESS

    &&& post == pre
}

pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& pre.sbuf[core].len() == 0

    &&& post == State {
        writes: Writes {
            tso: if core == pre.writes.core { set![] } else { pre.writes.tso },
            ..pre.writes
        },
        hist: if core == pre.writes.core { History { pending_maps: map![], ..pre.hist } } else { pre.hist },
        ..pre
    }
}

pub open spec fn step_SadWrite(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If we do a write without fulfilling the right conditions, we set happy to false.
    &&& lbl matches Lbl::Write(core, addr, value)
    &&& {
        ||| value & 1 == 1 && !pre.is_happy_writenonneg(core, addr, value)
        ||| value & 1 == 0 && !pre.is_happy_writenonpos(core, addr, value)
    }
    &&& !post.happy
}

pub open spec fn step_Sadness(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    // If happy is unset, arbitrary steps are allowed.
    &&& !pre.happy
    &&& !post.happy
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                    => step_Invlpg(pre, post, c, lbl),
        Step::MemOpNoTr { walk }        => step_MemOpNoTr(pre, post, c, walk, lbl),
        Step::MemOpTLB { tlb_va }       => step_MemOpTLB(pre, post, c, tlb_va, lbl),
        Step::WalkInit { core, vaddr }  => step_WalkInit(pre, post, c, core, vaddr, lbl),
        Step::WalkStep { core, walk }   => step_WalkStep(pre, post, c, core, walk, lbl),
        Step::TLBFill { core, walk }    => step_TLBFill(pre, post, c, core, walk, lbl),
        Step::TLBEvict { core, tlb_va } => step_TLBEvict(pre, post, c, core, tlb_va, lbl),
        Step::WriteNonneg               => step_WriteNonneg(pre, post, c, lbl),
        Step::WriteNonpos               => step_WriteNonpos(pre, post, c, lbl),
        Step::Writeback { core }        => step_Writeback(pre, post, c, core, lbl),
        Step::Read                      => step_Read(pre, post, c, lbl),
        Step::Barrier                   => step_Barrier(pre, post, c, lbl),
        Step::SadWrite                  => step_SadWrite(pre, post, c, lbl),
        Step::Sadness                   => step_Sadness(pre, post, c, lbl),
        Step::Stutter                   => step_Stutter(pre, post, c, lbl),
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

    #[verifier(opaque)]
    pub open spec fn wf_ptmem_range(self, c: Constants) -> bool {
        //self.pt_mem.mem.dom() === Set::new(|va| aligned(va as nat, 8) && c.in_ptmem_range(va as nat, 8))
        &&& forall|va| #[trigger] self.pt_mem.mem.contains_key(va)
            <==> aligned(va as nat, 8) && c.in_ptmem_range(va as nat, 8)
        &&& forall|i| #![auto] 0 <= i < self.writer_sbuf().len() ==> {
            &&& c.in_ptmem_range(self.writer_sbuf()[i].0 as nat, 8)
            &&& aligned(self.writer_sbuf()[i].0 as nat as nat, 8)
        }
    }

    pub open spec fn non_writer_sbufs_are_empty(self, c: Constants) -> bool {
        forall|core| #[trigger] c.valid_core(core) && core != self.writes.core
            ==> self.sbuf[core] === seq![]
    }

    pub open spec fn writer_sbuf_entries_are_unique(self) -> bool {
        forall|i1, i2| #![auto]
               0 <= i1 < self.writer_sbuf().len()
            && 0 <= i2 < self.writer_sbuf().len()
            && i1 != i2
                ==> self.writer_sbuf()[i2].0 != self.writer_sbuf()[i1].0
    }

    pub open spec fn writer_sbuf_entries_have_P_bit_0(self) -> bool {
        forall|i| #![auto] 0 <= i < self.writer_sbuf().len() ==> self.writer_sbuf()[i].1 & 1 == 0
    }

    pub open spec fn writer_sbuf_subset_tso_writes(self) -> bool {
        forall|a| self.writer_sbuf().contains_fst(a) ==> #[trigger] self.writes.tso.contains(a)
    }

    pub open spec fn inv_sbuf_facts(self, c: Constants) -> bool {
        &&& self.non_writer_sbufs_are_empty(c)
        &&& self.writer_sbuf_entries_are_unique()
        &&& self.writer_sbuf_subset_tso_writes()
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

    pub open spec fn inv_unmapping__inflight_walks(self, c: Constants) -> bool {
        forall|core, walk| c.valid_core(core) && #[trigger] self.walks[core].contains(walk) ==> {
            let walk_na = finish_iter_walk(self.core_mem(core), walk);
            let walk_a  = self.core_mem(core).pt_walk(walk.vaddr);
            &&& walk.vaddr < MAX_BASE
            &&& aligned(walk.vaddr as nat, 8)
            &&& walk.path.len() <= 3
            &&& !walk.complete
            // TODO: 
            // We could have more conditions and assumptions on what the page table looks like.
            // E.g. no "cycles" (configuring the page table in a way where a page table walk uses a
            // memory location more than once) and assume that we only unmap already-empty
            // directories.
            //
            // - If we unmap a directory that still has children, we can have inflight walks
            //   "caching" that part of the path. I.e. they may still complete successfully, so we
            //   have staleness due to non-atomicity/translation caching, not just TSO.
            //
            // - The issue is that enforcing these conditions might be more work than just not
            //   relying on them.
            // - Plus we'd need to prove them in the implementation
            //
            // Enforcing bottom-to-top unmapping:
            // - How to differentiate removal of a page mapping vs directory mapping?
            // - When we explicitly do separate memory ranges I could technically use the address
            //   to distinguish whether we're unmapping a page mapping or a directory mapping
            // - But this may not work generally with huge page mappings?
            //
            // Without bottom-to-top unmapping:
            // - We can now have in-flight walks that will complete successfully but don't satisfy
            //   is_iter_walk_prefix
            // - Specifically: If we remove a non-empty directory, walks using that directory may
            //   be in-progress and eventually complete successfully
            &&& (if walk_a.result() is Invalid {
                     walk_na.result() matches WalkResult::Valid { vbase, pte }
                         ==> self.hist.pending_unmaps.contains_pair(vbase, pte)
                 } else {
                     is_iter_walk_prefix(self.core_mem(core), walk)
                 })
        }
    }

    pub open spec fn inv_unmapping__valid_walk(self, c: Constants) -> bool {
        forall|va: usize, core| #![auto] c.valid_core(core) && va < MAX_BASE && self.core_mem(core).pt_walk(va).result() is Valid ==> {
            let core_walk = self.core_mem(core).pt_walk(va);
            let vbase = core_walk.result()->Valid_vbase;
            let pte = core_walk.result()->Valid_pte;
            let writer_walk = self.writer_mem().pt_walk(va);
            if self.hist.pending_unmaps.contains_key(vbase) {
                pte == self.hist.pending_unmaps[vbase]
            } else {
                core_walk == writer_walk
            }
        }
    }

}


#[verifier(opaque)]
pub open spec fn walk_next(mem: PTMem, walk: Walk) -> Walk {
    let Walk { vaddr, path, .. } = walk;
    let addr = if path.len() == 0 {
        add(mem.pml4, mul(l0_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 1 {
        add(path.last().1->Directory_addr, mul(l1_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 2 {
        add(path.last().1->Directory_addr, mul(l2_bits!(vaddr), WORD_SIZE))
    } else if path.len() == 3 {
        add(path.last().1->Directory_addr, mul(l3_bits!(vaddr), WORD_SIZE))
    } else { arbitrary() };

    let entry = PDE { entry: mem.read(addr), layer: Ghost(path.len()) }@;
    let walk = Walk {
        vaddr,
        path: path.push((addr, entry)),
        complete: !(entry is Directory),
    };
    walk
}

pub open spec fn is_iter_walk_prefix(mem: PTMem, walk: Walk) -> bool {
    let walkp0 = Walk { vaddr: walk.vaddr, path: seq![], complete: false };
    let walkp1 = walk_next(mem, walkp0);
    let walkp2 = walk_next(mem, walkp1);
    let walkp3 = walk_next(mem, walkp2);
    let walkp4 = walk_next(mem, walkp3);
    if walk.path.len() == 0 {
        walk == walkp0
    } else if walk.path.len() == 1 {
        walk == walkp1
    } else if walk.path.len() == 2 {
        &&& walk == walkp2
        &&& !walkp1.complete
    } else if walk.path.len() == 3 {
        &&& walk == walkp3
        &&& !walkp1.complete
        &&& !walkp2.complete
    } else if walk.path.len() == 4 {
        &&& walk == walkp4
        &&& !walkp1.complete
        &&& !walkp2.complete
        &&& !walkp3.complete
    } else {
        false
    }
}

pub open spec fn finish_iter_walk(mem: PTMem, walk: Walk) -> Walk {
    if walk.complete { walk } else {
        let walk = walk_next(mem, walk);
        if walk.complete { walk } else {
            let walk = walk_next(mem, walk);
            if walk.complete { walk } else {
                let walk = walk_next(mem, walk);
                if walk.complete { walk } else {
                    walk_next(mem, walk)
                }
            }
        }
    }
}

pub open spec fn iter_walk(mem: PTMem, vaddr: usize) -> Walk {
    let walk = walk_next(mem, Walk { vaddr, path: seq![], complete: false });
    if walk.complete { walk } else {
        let walk = walk_next(mem, walk);
        if walk.complete { walk } else {
            let walk = walk_next(mem, walk);
            if walk.complete { walk } else {
                walk_next(mem, walk)
            }
        }
    }
}

	#[verifier::external_body]
spec fn indexing_bits_match(va1: usize, va2: usize, len: nat) -> bool {
		unimplemented!()
	}


#[verifier::rlimit(100)] 
proof fn step_Writeback_preserves_inv_unmapping__inflight_walks(pre: State, post: State, c: Constants, step: Step, lbl: Lbl)
    requires
        step is Writeback,
        pre.wf(c),
        pre.happy,
        post.happy,
        post.polarity is Unmapping,
        pre.inv_sbuf_facts(c),
        pre.writer_sbuf_entries_have_P_bit_0(),
        pre.inv_unmapping__inflight_walks(c),
        pre.inv_unmapping__valid_walk(c),
        pre.inv_unmapping__core_vs_writer_reads(c),
        post.inv_unmapping__core_vs_writer_reads(c),
        post.inv_sbuf_facts(c),
        post.inv_unmapping__valid_walk(c),
        next_step(pre, post, c, step, lbl),
    ensures post.inv_unmapping__inflight_walks(c)
{
}


}
