use vstd::prelude::*;
use vstd::assert_by_contradiction;

fn main() {}

verus!{
global size_of usize == 8;

// File: spec_t/mmu/rl3.rs
pub mod rl3 {
use vstd::prelude::*;
use crate::{Core, Walk, PTE, PTMem};


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
    pub pending_maps: Map<usize, PTE>,
    pub pending_unmaps: Map<usize, PTE>,
}
}



// File: spec_t/mmu/pt_mem.rs
pub struct PTMem {
    pub mem: Map<usize, usize>,
    pub pml4: usize,
}

impl PTMem {

    pub open spec fn read(self, addr: usize) -> usize {
        self.mem[addr]
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

    pub open spec fn is_base_pt_walk(self, vaddr: usize) -> bool {
        &&& vaddr < MAX_BASE
        &&& self.pt_walk(vaddr).result() matches WalkResult::Valid { vbase, pte }
        &&& vbase == vaddr
    }

    #[verifier(opaque)]
    pub open spec fn view(self) -> Map<usize,PTE> {
        Map::new(
            |va| self.is_base_pt_walk(va),
            |va| self.pt_walk(va).result()->pte
        )
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

pub const MASK_FLAG_P: usize = bit!(0usize);

pub const MASK_FLAG_RW: usize = bit!(1usize);

pub const MASK_FLAG_US: usize = bit!(2usize);

pub const MASK_FLAG_PWT: usize = bit!(3usize);

pub const MASK_FLAG_PCD: usize = bit!(4usize);

pub const MASK_FLAG_XD: usize = bit!(63usize);

pub const MASK_PG_FLAG_G: usize = bit!(8usize);

pub const MASK_PG_FLAG_PAT: usize = bit!(12usize);

pub const MASK_L1_PG_FLAG_PS: usize = bit!(7usize);

pub const MASK_L2_PG_FLAG_PS: usize = bit!(7usize);

pub const MASK_L3_PG_FLAG_PAT: usize = bit!(7usize);

pub const MASK_DIRTY_ACCESS: usize = bit!(5) | bit!(6);
pub const MASK_NEG_DIRTY_ACCESS: usize = !MASK_DIRTY_ACCESS;

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

#[repr(transparent)]
pub struct PDE {
    pub entry: usize,
    pub layer: Ghost<nat>,
}

impl PDE {

	#[verifier::external_body]
    pub broadcast proof fn lemma_view_unchanged_dirty_access(self, other: PDE)
        requires
            self.layer@ < 4,
            #[trigger] (self.entry & MASK_NEG_DIRTY_ACCESS)
                == #[trigger] (other.entry & MASK_NEG_DIRTY_ACCESS),
            self.layer == other.layer,
        ensures other@ == self@
	{
		unimplemented!()
	}

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


	#[verifier::external_body]
pub proof fn lemma_bit_indices_less_512(va: usize)
    ensures
        l0_bits!(va) < 512,
        l1_bits!(va) < 512,
        l2_bits!(va) < 512,
        l3_bits!(va) < 512,
	{
		unimplemented!()
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


pub const X86_NUM_LAYERS: usize = 4;

pub const X86_NUM_ENTRIES: usize = 512;

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

pub const L0_ENTRY_SIZE: usize = 512 * L1_ENTRY_SIZE;

pub open spec fn index_from_offset(offset: nat, entry_size: nat) -> (res: nat)
    recommends entry_size > 0,
{
    offset / entry_size
}

pub open spec fn index_from_base_and_addr(base: nat, addr: nat, entry_size: nat) -> nat
    recommends
        addr >= base,
        entry_size > 0,
{
    index_from_offset(sub(addr, base), entry_size)
}

pub open spec fn entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + idx * entry_size
}

pub open spec fn next_entry_base_from_index(base: nat, idx: nat, entry_size: nat) -> nat {
    base + (idx + 1) * entry_size
}

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
    pub open spec(checked) fn index_for_vaddr(self, layer: nat, base: nat, vaddr: nat) -> nat
        recommends
            self.inv(),
            layer < self.layers.len(),
            base <= vaddr,
    {
        index_from_base_and_addr(base, vaddr, self.entry_size(layer))
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

	#[verifier::external_body]
pub proof fn x86_arch_spec_upper_bound()
    ensures
        x86_arch_spec.upper_vaddr(0, 0) == 512 * 512 * 1024 * 1024 * 1024,
        x86_arch_spec.upper_vaddr(0, 0) == MAX_BASE
	{
		unimplemented!()
	}


// File: impl_u/l1.rs
pub mod l1 {
use vstd::prelude::*;
use crate::PTE;
use crate::Arch;


pub enum NodeEntry {
    Directory(Directory),
    Page(PTE),
    Invalid,
}

pub struct Directory {
    pub entries: Seq<NodeEntry>,
    pub layer: nat, // index into layer_sizes
    pub base_vaddr: nat,
    pub arch: Arch,
}

impl NodeEntry {

    pub open spec fn interp(self, base: nat) -> Map<nat, PTE>
        decreases self, 0nat, 0nat
    {
        match self {
            NodeEntry::Page(p)      => map![base => p],
            NodeEntry::Directory(d) => d.interp_aux(0),
            NodeEntry::Invalid      => map![],
        }
    }

}


impl Directory {

    pub open spec(checked) fn well_formed(&self) -> bool {
        &&& self.arch.inv()
        &&& self.layer < self.arch.layers.len()
        //&&& aligned(self.base_vaddr, self.entry_size() * self.num_entries())
        &&& self.entries.len() == self.num_entries()
    }

    pub open spec(checked) fn entry_size(&self) -> nat
        recommends self.layer < self.arch.layers.len()
    {
        self.arch.entry_size(self.layer)
    }

    pub open spec(checked) fn num_entries(&self) -> nat // number of entries
        recommends self.layer < self.arch.layers.len()
    {
        self.arch.num_entries(self.layer)
    }

    pub open spec(checked) fn pages_match_entry_size(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| (i < self.entries.len() && self.entries[i as int] is Page)
            ==> (#[trigger] self.entries[i as int]->Page_0.frame.size) == self.entry_size()
    }

    pub open spec(checked) fn directories_are_in_next_layer(&self) -> bool
        recommends self.well_formed()
    {
        forall|i: nat| i < self.entries.len() && self.entries.index(i as int) is Directory ==> {
            let directory = #[trigger] self.entries[i as int]->Directory_0;
            &&& directory.layer == self.layer + 1
            &&& directory.base_vaddr == self.base_vaddr + i * self.entry_size()
        }
    }

    pub open spec(checked) fn directories_obey_invariant(&self) -> bool
        recommends
            self.well_formed(),
            self.directories_are_in_next_layer(),
            self.directories_match_arch(),
        decreases self.arch.layers.len() - self.layer, 0nat
    {
        if self.well_formed() && self.directories_are_in_next_layer() && self.directories_match_arch() {
            forall|i: nat| (i < self.entries.len() && #[trigger] self.entries[i as int] is Directory)
                ==> self.entries[i as int]->Directory_0.inv()
        } else {
            arbitrary()
        }
    }

    pub open spec(checked) fn directories_match_arch(&self) -> bool {
        forall|i: nat| (i < self.entries.len() && self.entries.index(i as int) is Directory)
            ==> (#[trigger] self.entries.index(i as int)->Directory_0.arch) == self.arch
    }

    pub open spec(checked) fn inv(&self) -> bool
        decreases self.arch.layers.len() - self.layer
    {
        &&& self.well_formed()
        &&& self.pages_match_entry_size()
        &&& self.directories_are_in_next_layer()
        &&& self.directories_match_arch()
        &&& self.directories_obey_invariant()
        //&&& non_empty ==> self.directories_are_nonempty()
        // &&& self.frames_aligned()
    }

    pub open spec(checked) fn interp(self) -> Map<nat, PTE> {
        self.interp_aux(0)
    }

    pub open spec(checked) fn upper_vaddr(self) -> nat
        recommends self.well_formed()
    {
        self.arch.upper_vaddr(self.layer, self.base_vaddr)
    }

    pub open spec fn index_for_vaddr(self, vaddr: nat) -> nat {
        self.arch.index_for_vaddr(self.layer, self.base_vaddr, vaddr)
    }

    pub open spec fn entry_base(self, idx: nat) -> nat {
        self.arch.entry_base(self.layer, self.base_vaddr, idx)
    }

    pub open spec fn interp_of_entry(self, entry: nat) -> Map<nat, PTE>
        decreases self, self.entries.len() - entry, 1nat
    {
        if entry < self.entries.len() {
            self.entries[entry as int].interp(self.entry_base(entry))
        } else {
            arbitrary()
        }
    }

    pub open spec fn interp_aux(self, i: nat) -> Map<nat, PTE>
        decreases self, self.entries.len() - i, 2nat
    {
        if i < self.entries.len() {
            self.interp_aux(i + 1).union_prefer_right(self.interp_of_entry(i))
        } else { // i < self.entries.len()
            map![]
        }
    }

	#[verifier::external_body]
    pub broadcast proof fn lemma_interp_aux_between(self, i: nat, va: nat, pte: PTE)
        requires
            #[trigger] self.inv(),
            #[trigger] self.interp_aux(i).contains_pair(va, pte),
        ensures
            self.entry_base(i) <= va < self.upper_vaddr(),
            self.entry_base(i) < va + self.interp_aux(i)[va].frame.size <= self.upper_vaddr(),
        decreases self, self.entries.len() - i, 1nat
	{
		unimplemented!()
	}

	#[verifier::external_body]
    pub proof fn lemma_interp_contains_key_implies_interp_of_entry_contains_key_at_index(self, vaddr: nat) by (nonlinear_arith)
        requires
            self.inv(),
            self.interp().contains_key(vaddr),
        ensures
            self.interp_of_entry(self.index_for_vaddr(vaddr)).contains_key(vaddr),
            self.interp_of_entry(self.index_for_vaddr(vaddr)).contains_pair(vaddr, self.interp()[vaddr])
	{
		unimplemented!()
	}

}
}


// File: impl_u/l2_impl.rs
impl PDE {

    pub open spec fn hp_pat_is_zero(self) -> bool {
        &&& self@ is Page && self.layer == 1 ==> self.entry & MASK_PG_FLAG_PAT == 0
        &&& self@ is Page && self.layer == 2 ==> self.entry & MASK_PG_FLAG_PAT == 0
    }

}


#[verifier::ext_equal]
pub struct PTDir {
    /// Region of physical memory in which this PTDir is stored
    pub region: MemRegion,
    pub entries: Seq<Option<PTDir>>,
    /// reflexive-transitive closure of `region` over `entries`
    pub used_regions: Set<MemRegion>,
}

pub mod PT {

use super::*;
use crate::l1;

pub open spec(checked) fn inv(tok: WrappedTokenView, pt: PTDir) -> bool {
    &&& pt.region.base == tok.pt_mem.pml4
    &&& inv_at(tok, pt, 0, tok.pt_mem.pml4)
}

pub open spec fn entry_at_spec(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, i: nat) -> PDE {
    PDE {
        entry: tok.read(i as usize, pt.region),
        layer: Ghost(layer),
    }
}

pub open spec fn ghost_pt_matches_structure(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| #![trigger pt.entries[i as int], entry_at_spec(tok, pt, layer, ptr, i)@]
    i < X86_NUM_ENTRIES ==> {
        let entry = entry_at_spec(tok, pt, layer, ptr, i)@;
        entry is Directory <==> pt.entries[i as int] is Some
    }
}

pub open spec fn invalid_entries_are_zeroed(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| i < X86_NUM_ENTRIES ==>
        (#[trigger] entry_at_spec(tok, pt, layer, ptr, i))@ is Invalid ==> tok.regions[pt.region][i as int] == 0
}

pub open spec fn directories_obey_invariant_at(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool
    decreases X86_NUM_LAYERS - layer, 0nat
        when layer_in_range(layer)
{
    forall|i: nat| i < X86_NUM_ENTRIES ==> {
        (#[trigger] entry_at_spec(tok, pt, layer, ptr, i))@ matches GPDE::Directory { addr, ..}
            ==> inv_at(tok, pt.entries[i as int]->Some_0, layer + 1, addr)
    }
}

pub open spec(checked) fn layer_in_range(layer: nat) -> bool {
    layer < X86_NUM_LAYERS
}

pub open spec(checked) fn inv_at(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool
    decreases X86_NUM_LAYERS - layer
{
    &&& aligned(ptr as nat, PAGE_SIZE as nat)
    &&& tok.regions.contains_key(pt.region)
    &&& pt.region.base == ptr
    &&& pt.region.size == PAGE_SIZE
    &&& tok.regions[pt.region].len() == pt.entries.len()
    &&& layer_in_range(layer)
    &&& pt.entries.len() == X86_NUM_ENTRIES
    &&& invalid_entries_are_zeroed(tok, pt, layer, ptr)
    &&& directories_obey_invariant_at(tok, pt, layer, ptr)
    &&& directories_have_flags(tok, pt, layer, ptr)
    &&& ghost_pt_matches_structure(tok, pt, layer, ptr)
    &&& ghost_pt_used_regions_rtrancl(tok, pt, layer, ptr)
    &&& ghost_pt_used_regions_pairwise_disjoint(tok, pt, layer, ptr)
    &&& ghost_pt_region_notin_used_regions(tok, pt, layer, ptr)
    &&& pt.used_regions.subset_of(tok.regions.dom())
    &&& hp_pat_is_zero(tok, pt, layer, ptr)
    &&& entry_mb0_bits_are_zero(tok, pt, layer, ptr)
}

pub open spec fn directories_have_flags(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| i < X86_NUM_ENTRIES ==> {
        (#[trigger] entry_at_spec(tok, pt, layer, ptr, i)@) matches GPDE::Directory { RW, US, XD, .. } ==> RW && US && !XD
    }
}

pub open spec fn entry_mb0_bits_are_zero(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| i < X86_NUM_ENTRIES ==>
        (#[trigger] entry_at_spec(tok, pt, layer, ptr, i)).all_mb0_bits_are_zero()
}

pub open spec fn hp_pat_is_zero(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| #![auto] i < X86_NUM_ENTRIES ==> entry_at_spec(tok, pt, layer, ptr, i).hp_pat_is_zero()
}

	#[verifier::external_body]
pub open spec fn ghost_pt_used_regions_pairwise_disjoint(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
		unimplemented!()
	}


pub open spec fn ghost_pt_region_notin_used_regions(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat|
        i < pt.entries.len() && pt.entries[i as int] is Some
        ==> !(#[trigger] pt.entries[i as int]->Some_0.used_regions.contains(pt.region))
}

pub open spec fn ghost_pt_used_regions_rtrancl(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    // reflexive
    &&& pt.used_regions.contains(pt.region)
    // transitive
    &&& forall|i: nat, r: MemRegion| #![trigger pt.entries[i as int]->Some_0.used_regions.contains(r), pt.used_regions.contains(r)]
            i < pt.entries.len() && pt.entries[i as int] is Some &&
            pt.entries[i as int]->Some_0.used_regions.contains(r)
            ==> pt.used_regions.contains(r)
}

pub open spec fn interp_at(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat) -> l1::Directory
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES, 2nat
        when inv_at(tok, pt, layer, ptr)
{
    l1::Directory {
        entries: interp_at_aux(tok, pt, layer, ptr, base_vaddr, seq![]),
        layer: layer,
        base_vaddr,
        arch: x86_arch_spec,
    }
}

pub open spec fn interp_at_entry(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, idx: nat) -> l1::NodeEntry
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - idx, 0nat
        when inv_at(tok, pt, layer, ptr)
{
    match entry_at_spec(tok, pt, layer, ptr, idx)@ {
        GPDE::Directory { addr: dir_addr, .. } => {
            let entry_base = x86_arch_spec.entry_base(layer, base_vaddr, idx);
            l1::NodeEntry::Directory(interp_at(tok, pt.entries[idx as int]->Some_0, layer + 1, dir_addr, entry_base))
        },
        GPDE::Page { addr, RW, US, XD, .. } =>
            l1::NodeEntry::Page(
                PTE {
                    frame: MemRegion { base: addr as nat, size: x86_arch_spec.entry_size(layer) },
                    flags: Flags {
                        is_writable:     RW,
                        is_supervisor:   !US,
                        disable_execute: XD,
                    },
                }),
        GPDE::Invalid => l1::NodeEntry::Invalid,
    }
}

pub open spec fn interp_at_aux(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base_vaddr: nat, init: Seq<l1::NodeEntry>) -> Seq<l1::NodeEntry>
    decreases X86_NUM_LAYERS - layer, X86_NUM_ENTRIES - init.len(), 1nat
        when inv_at(tok, pt, layer, ptr)
{
    if init.len() >= X86_NUM_ENTRIES {
        init
    } else {
        let entry = interp_at_entry(tok, pt, layer, ptr, base_vaddr, init.len());
        interp_at_aux(tok, pt, layer, ptr, base_vaddr, init.push(entry))
    }
}

pub open spec fn interp(tok: WrappedTokenView, pt: PTDir) -> l1::Directory {
    interp_at(tok, pt, 0, tok.pt_mem.pml4, 0)
}

	#[verifier::external_body]
#[verifier(spinoff_prover)]
pub broadcast proof fn lemma_inv_implies_interp_inv(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base: nat)
    requires
        inv_at(tok, pt, layer, ptr),
        layer < x86_arch_spec.layers.len(),
    ensures
        #[trigger] interp_at(tok, pt, layer, ptr, base).inv()
    decreases X86_NUM_LAYERS - layer
	{
		unimplemented!()
	}

	#[verifier::external_body]
#[verifier::spinoff_prover]
pub proof fn lemma_interp_at_facts(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize, base: nat)
    requires
        inv_at(tok, pt, layer, ptr),
        //interp_at(tok, pt, layer, ptr, base).inv(ne),
    ensures
        interp_at(tok, pt, layer, ptr, base).base_vaddr     == base,
        interp_at(tok, pt, layer, ptr, base).upper_vaddr()  == x86_arch_spec.upper_vaddr(layer, base),
        interp_at(tok, pt, layer, ptr, base).entries.len()  == X86_NUM_ENTRIES,
        //interp_at(tok, pt, layer, ptr, base).interp().lower == base,
        //interp_at(tok, pt, layer, ptr, base).interp().upper == x86_arch_spec.upper_vaddr(layer, base),
        ({ let res = interp_at(tok, pt, layer, ptr, base);
           forall|j: nat| j < res.entries.len() ==> res.entries[j as int] === #[trigger] interp_at_entry(tok, pt, layer, ptr, base, j)
        }),
	{
		unimplemented!()
	}
}

// File: impl_u/wrapped_token.rs
pub enum OpArgs {
    Map { base: usize, pte: PTE },
    Unmap { base: usize },
}

pub struct WrappedTokenView {
    pub orig_st: os::State,
    pub args: OpArgs,
    pub change_made: bool,
    pub regions: Map<MemRegion, Seq<usize>>,
    /// We also keep the flat memory directly because this is what the MMU's interpretation is
    /// defined on.
    pub pt_mem: crate::PTMem,
    // result is only relevant for mapping (TODO: and maybe we can get rid of it there?)
    pub result: Result<(),()>,
}

impl WrappedTokenView {

    pub open spec fn read(self, idx: usize, r: MemRegion) -> usize {
        self.regions[r][idx as int] & MASK_NEG_DIRTY_ACCESS
    }

    pub open spec fn regions_derived_from_view(self) -> bool {
        forall|r| self.regions.contains_key(r) ==> #[trigger] self.regions[r] == Seq::new(512, |i: int| self.pt_mem.mem[(r.base + i * 8) as usize])
    }

    #[verifier::rlimit(200)]
    pub proof fn lemma_interps_match_aux1(self, pt: PTDir)
        requires
            PT::inv(self, pt),
            self.regions_derived_from_view(),
        ensures PT::interp(self, pt).interp().dom().subset_of(self.pt_mem@.dom().map(|k| k as nat))
    {
        reveal(crate::PTMem::view);
        assert forall|vaddr: nat|
            PT::interp(self, pt).interp().contains_key(vaddr)
                implies {
            &&& vaddr <= usize::MAX
            &&& self.pt_mem.is_base_pt_walk(vaddr as usize)
        } by {
            x86_arch_spec_upper_bound();
            assert_by_contradiction!(vaddr < MAX_BASE, {
                assert_by_contradiction!(!PT::interp(self, pt).interp().contains_key(vaddr), {
                    broadcast use crate::PT::lemma_inv_implies_interp_inv;
                    PT::interp(self, pt).lemma_interp_aux_between(0, vaddr, PT::interp(self, pt).interp()[vaddr]);
                });
            });
            assert(vaddr == vaddr as usize);
            let vaddr: usize = vaddr as usize;
            PT::lemma_interp_at_facts(self, pt, 0, self.pt_mem.pml4, 0);
            lemma_bit_indices_less_512(vaddr as usize);
            assert(forall|x: usize, b: usize| x & b & b == x & b) by (bit_vector);

            let l0_bidx = l0_bits!(vaddr);
            let l1_bidx = l1_bits!(vaddr);
            let l2_bidx = l2_bits!(vaddr);
            let l3_bidx = l3_bits!(vaddr);

            let l0_idx = mul(l0_bits!(vaddr), WORD_SIZE);
            let l1_idx = mul(l1_bits!(vaddr), WORD_SIZE);
            let l2_idx = mul(l2_bits!(vaddr), WORD_SIZE);
            let l3_idx = mul(l3_bits!(vaddr), WORD_SIZE);
            assert(forall|a:usize| (a & bitmask_inc!(0usize,8usize) == a) ==> a < 512) by (bit_vector);
            assert(bitmask_inc!(39usize,47usize) == 0xFF80_0000_0000) by (compute);
            assert(bitmask_inc!(30usize,38usize) == 0x007F_C000_0000) by (compute);
            assert(bitmask_inc!(21usize,29usize) == 0x0000_3FE0_0000) by (compute);
            assert(bitmask_inc!(12usize,20usize) == 0x0000_001F_F000) by (compute);
            let interp_l0 = PT::interp(self, pt);
            let interp_l0_entry = PT::interp_at_entry(self, pt, 0, self.pt_mem.pml4, 0, l0_bidx as nat);
            crate::PT::lemma_inv_implies_interp_inv(self, pt, 0, self.pt_mem.pml4, 0);
            interp_l0.lemma_interp_contains_key_implies_interp_of_entry_contains_key_at_index(vaddr as nat);
            assert(interp_l0.index_for_vaddr(vaddr as nat) == x86_arch_spec.index_for_vaddr(0, 0, vaddr as nat));
            assert(interp_l0.interp_of_entry(interp_l0.index_for_vaddr(vaddr as nat)).contains_key(vaddr as nat));
            let l0_addr = add(self.pt_mem.pml4, l0_idx);
            let l0e = PDE { entry: self.pt_mem.read(l0_addr), layer: Ghost(0) };
            let impl_l0e = PT::entry_at_spec(self, pt, 0, self.pt_mem.pml4, l0_bidx as nat);
            assert(self.pt_mem.read(l0_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l0_bidx as nat as usize, pt.region));
            assert(l0e@ == impl_l0e@) by {
                l0e.lemma_view_unchanged_dirty_access(impl_l0e);
            };

            let low_bits: usize = vaddr % (L0_ENTRY_SIZE as usize);
            // This assert proves: ... == l0_bidx * L0_ENTRY_SIZE + low_bits
            assert((l0_bidx << 39usize) | low_bits
                   == add(mul(l0_bidx, mul(512, mul(512, mul(512, 4096)))),
                          low_bits)) by (bit_vector)
                requires
                    low_bits == vaddr % mul(512, mul(512, mul(512, 4096)));
            assert(vaddr == ((l0_bidx << 39usize) | low_bits)) by (bit_vector)
                requires
                    l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                    vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                    low_bits == vaddr % mul(512, mul(512, mul(512, 4096)));

            match l0e@ {
                GPDE::Directory { addr: l1_daddr, .. } => {
                    assert(interp_l0_entry is Directory);
                    let l1_addr = add(l1_daddr, l1_idx);
                    let l1e = PDE { entry: self.pt_mem.read(l1_addr), layer: Ghost(1) };
                    let l1_base = x86_arch_spec.entry_base(0, 0, l0_bidx as nat);
                    let l1_ghost_pt = pt.entries[l0_bidx as int]->Some_0;
                    assert(PT::directories_obey_invariant_at(self, pt, 0, self.pt_mem.pml4));
                    assert(PT::inv_at(self, l1_ghost_pt, 1, l1_daddr));
                    PT::lemma_interp_at_facts(self, l1_ghost_pt, 1, l1_daddr, l1_base);
                    let interp_l1 = PT::interp_at(self, l1_ghost_pt, 1, l1_daddr, l1_base);
                    let interp_l1_entry = PT::interp_at_entry(self, l1_ghost_pt, 1, l1_daddr, l1_base, l1_bidx as nat);
                    crate::PT::lemma_inv_implies_interp_inv(self, l1_ghost_pt, 1, l1_daddr, l1_base);
                    interp_l1.lemma_interp_contains_key_implies_interp_of_entry_contains_key_at_index(vaddr as nat);
                    assert(interp_l1.interp_of_entry(interp_l1.index_for_vaddr(vaddr as nat)).contains_key(vaddr as nat));

                    let impl_l1e = PT::entry_at_spec(self, l1_ghost_pt, 1, l1_daddr, l1_bidx as nat);
                    assert(l1e@ == impl_l1e@) by {
                        assert(self.pt_mem.read(l1_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l1_bidx, l1_ghost_pt.region));
                        l1e.lemma_view_unchanged_dirty_access(impl_l1e);
                    };

                    let low_bits = vaddr % L1_ENTRY_SIZE;
                    // This assert proves: ... == l0_bidx * L0_ENTRY_SIZE + l1_bidx * L1_ENTRY_SIZE + low_bits
                    assert((l0_bidx << 39usize) | (l1_bidx << 30usize) | low_bits
                           == add(add(mul(l0_bidx, mul(512, mul(512, mul(512, 4096)))),
                                      mul(l1_bidx, mul(512, mul(512, 4096)))),
                                      low_bits)) by (bit_vector)
                        requires
                            l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                            low_bits == vaddr % mul(512, mul(512, 4096));
                    assert(vaddr == ((l0_bidx << 39usize) | (l1_bidx << 30usize) | low_bits)) by (bit_vector)
                        requires
                            l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                            l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                            vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                            low_bits == vaddr % mul(512, mul(512, 4096));

                    match l1e@ {
                        GPDE::Page { addr: page_addr, .. } => {
                            let l2_base = x86_arch_spec.entry_base(1, l1_base, l1_bidx as nat);
                            assert(aligned(l2_base, L1_ENTRY_SIZE as nat)) by {
                                crate::lemma_entry_base_from_index(l1_base, l1_bidx as nat, L1_ENTRY_SIZE as nat);
                            };
                            assert(interp_l1.interp_of_entry(l1_bidx as nat).dom() =~= set![l2_base as nat]);
                            assert(self.pt_mem.is_base_pt_walk(vaddr));
                        },
                        GPDE::Directory { addr: l2_daddr, .. } => {
                            assert(interp_l1_entry is Directory);
                            let l2_addr = add(l2_daddr, l2_idx);
                            let l2e = PDE { entry: self.pt_mem.read(l2_addr), layer: Ghost(2) };
                            let l2_base = x86_arch_spec.entry_base(1, l1_base, l1_bidx as nat);
                            let l2_ghost_pt = l1_ghost_pt.entries[l1_bidx as int]->Some_0;
                            assert(PT::directories_obey_invariant_at(self, l1_ghost_pt, 1, l1_daddr));
                            assert(PT::inv_at(self, l2_ghost_pt, 2, l2_daddr));
                            PT::lemma_interp_at_facts(self, l2_ghost_pt, 2, l2_daddr, l2_base);
                            let interp_l2 = PT::interp_at(self, l2_ghost_pt, 2, l2_daddr, l2_base);
                            let interp_l2_entry = PT::interp_at_entry(self, l2_ghost_pt, 2, l2_daddr, l2_base, l2_bidx as nat);
                            crate::PT::lemma_inv_implies_interp_inv(self, l2_ghost_pt, 2, l2_daddr, l2_base);
                            interp_l2.lemma_interp_contains_key_implies_interp_of_entry_contains_key_at_index(vaddr as nat);
                            assert(interp_l2.interp_of_entry(interp_l2.index_for_vaddr(vaddr as nat)).contains_key(vaddr as nat));

                            let impl_l2e = PT::entry_at_spec(self, l2_ghost_pt, 2, l2_daddr, l2_bidx as nat);
                            assert(l2e@ == impl_l2e@) by {
                                assert(self.pt_mem.read(l2_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l2_bidx, l2_ghost_pt.region));
                                l2e.lemma_view_unchanged_dirty_access(impl_l2e);
                            };

                            let low_bits: usize = vaddr % (L2_ENTRY_SIZE as usize);
                            // This assert proves: ... == l0_bidx * L0_ENTRY_SIZE + l1_bidx * L1_ENTRY_SIZE + l2_bidx * L2_ENTRY_SIZE + low_bits
                            assert((l0_bidx << 39usize) | (l1_bidx << 30usize) | (l2_bidx << 21usize) | low_bits
                                   == add(add(add(
                                          mul(l0_bidx, mul(512, mul(512, mul(512, 4096)))),
                                          mul(l1_bidx, mul(512, mul(512, 4096)))),
                                          mul(l2_bidx, mul(512, 4096))),
                                          low_bits)) by (bit_vector)
                                requires
                                    l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                    l2_bidx == (vaddr & 0x0000_3FE0_0000) >> 21,
                                    low_bits == vaddr % mul(512, 4096);
                            assert(vaddr == ((l0_bidx << 39usize) | (l1_bidx << 30usize) | (l2_bidx << 21usize) | low_bits)) by (bit_vector)
                                requires
                                    l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                                    l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                    l2_bidx == (vaddr & 0x0000_3FE0_0000) >> 21,
                                    vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                                    low_bits == vaddr % mul(512, 4096);

                            match l2e@ {
                                GPDE::Page { addr: page_addr, .. } => {
                                    let l3_base = x86_arch_spec.entry_base(2, l2_base, l2_bidx as nat);
                                    assert(aligned(l3_base, L2_ENTRY_SIZE as nat)) by {
                                        crate::lemma_entry_base_from_index(0, l0_bidx as nat, L0_ENTRY_SIZE as nat);
                                        crate::lemma_entry_base_from_index(l1_base, l1_bidx as nat, L1_ENTRY_SIZE as nat);
                                        crate::lemma_entry_base_from_index(l2_base, l2_bidx as nat, L2_ENTRY_SIZE as nat);
                                    };
                                    assert(interp_l2.interp_of_entry(l2_bidx as nat).dom() =~= set![l3_base as nat]);
                                    assert(align_to_usize(vaddr, L2_ENTRY_SIZE) == vaddr);
                                    assert(self.pt_mem.is_base_pt_walk(vaddr));
                                },
                                GPDE::Directory { addr: l3_daddr, .. } => {
                                    assert(interp_l2_entry is Directory);
                                    let l3_addr = add(l3_daddr, l3_idx);
                                    let l3e = PDE { entry: self.pt_mem.read(l3_addr), layer: Ghost(3) };
                                    let l3_base = x86_arch_spec.entry_base(2, l2_base, l2_bidx as nat);
                                    let l3_ghost_pt = l2_ghost_pt.entries[l2_bidx as int]->Some_0;
                                    assert(PT::directories_obey_invariant_at(self, l2_ghost_pt, 2, l2_daddr));
                                    assert(PT::inv_at(self, l3_ghost_pt, 3, l3_daddr));
                                    PT::lemma_interp_at_facts(self, l3_ghost_pt, 3, l3_daddr, l3_base);
                                    let interp_l3 = PT::interp_at(self, l3_ghost_pt, 3, l3_daddr, l3_base);
                                    let interp_l3_entry = PT::interp_at_entry(self, l3_ghost_pt, 3, l3_daddr, l3_base, l3_bidx as nat);
                                    crate::PT::lemma_inv_implies_interp_inv(self, l3_ghost_pt, 3, l3_daddr, l3_base);
                                    interp_l3.lemma_interp_contains_key_implies_interp_of_entry_contains_key_at_index(vaddr as nat);
                                    assert(interp_l3.interp_of_entry(interp_l3.index_for_vaddr(vaddr as nat)).contains_key(vaddr as nat));

                                    let impl_l3e = PT::entry_at_spec(self, l3_ghost_pt, 3, l3_daddr, l3_bidx as nat);
                                    assert(l3e@ == impl_l3e@) by {
                                        assert(self.pt_mem.read(l3_addr) & MASK_NEG_DIRTY_ACCESS == self.read(l3_bidx, l3_ghost_pt.region));
                                        l3e.lemma_view_unchanged_dirty_access(impl_l3e);
                                    };

                                    let low_bits = vaddr % L3_ENTRY_SIZE;
                                    // This assert proves: ... == l0_bidx * L0_ENTRY_SIZE + l1_bidx * L1_ENTRY_SIZE + l2_bidx * L2_ENTRY_SIZE + l3_bidx * L3_ENTRY_SIZE + low_bits
                                    assert((l0_bidx << 39usize) | (l1_bidx << 30usize) | (l2_bidx << 21usize) | (l3_bidx << 12usize) | low_bits
                                           == add(add(add(add(
                                                  mul(l0_bidx, mul(512, mul(512, mul(512, 4096)))),
                                                  mul(l1_bidx, mul(512, mul(512, 4096)))),
                                                  mul(l2_bidx, mul(512, 4096))),
                                                  mul(l3_bidx, 4096)),
                                                  low_bits)) by (bit_vector)
                                        requires
                                            l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                            l2_bidx == (vaddr & 0x0000_3FE0_0000) >> 21,
                                            l3_bidx == (vaddr & 0x0000_001F_F000) >> 12,
                                            low_bits == vaddr % 4096;
                                    assert(vaddr == ((l0_bidx << 39usize) | (l1_bidx << 30usize) | (l2_bidx << 21usize) | (l3_bidx << 12usize) | low_bits)) by (bit_vector)
                                        requires
                                            l0_bidx == (vaddr & 0xFF80_0000_0000) >> 39,
                                            l1_bidx == (vaddr & 0x007F_C000_0000) >> 30,
                                            l2_bidx == (vaddr & 0x0000_3FE0_0000) >> 21,
                                            l3_bidx == (vaddr & 0x0000_001F_F000) >> 12,
                                            vaddr < mul(512usize, mul(512, mul(512, mul(512, 4096)))),
                                            low_bits == vaddr % 4096;

                                    match l3e@ {
                                        GPDE::Page { addr: page_addr, .. } => {
                                            let l4_base = x86_arch_spec.entry_base(3, l3_base, l3_bidx as nat);
                                            assert(aligned(l4_base, L3_ENTRY_SIZE as nat)) by {
                                                crate::lemma_entry_base_from_index(0, l0_bidx as nat, L0_ENTRY_SIZE as nat);
                                                crate::lemma_entry_base_from_index(l1_base, l1_bidx as nat, L1_ENTRY_SIZE as nat);
                                                crate::lemma_entry_base_from_index(l2_base, l2_bidx as nat, L2_ENTRY_SIZE as nat);
                                                crate::lemma_entry_base_from_index(l3_base, l3_bidx as nat, L3_ENTRY_SIZE as nat);
                                            };
                                            assert(interp_l3.interp_of_entry(l3_bidx as nat).dom() =~= set![l4_base as nat]);
                                            assert(align_to_usize(vaddr, L3_ENTRY_SIZE) == vaddr);
                                            assert(self.pt_mem.is_base_pt_walk(vaddr));
                                        },
                                        GPDE::Directory { .. } => assert(false),
                                        GPDE::Invalid => assert(false),
                                    }
                                },
                                GPDE::Invalid => assert(false),
                            }
                        },
                        GPDE::Invalid => assert(false),
                    }
                },
                GPDE::Page { .. } => assert(false),
                GPDE::Invalid => {
                    assert(!interp_l0.interp().contains_key(vaddr as nat));
                },
            };
        }
        assert forall|vaddr: nat|
            PT::interp(self, pt).interp().contains_key(vaddr)
                implies {
            &&& vaddr <= usize::MAX
            &&& self.pt_mem@.contains_key(vaddr as usize)
        } by {
            assert(forall|vaddr: usize| #![auto] self.pt_mem.is_base_pt_walk(vaddr) ==> self.pt_mem@.contains_key(vaddr));
        }
    }

}



// File: spec_t/os.rs
pub mod os {
use vstd::prelude::*;
use crate::{PTE, Core};

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
}

// File: spec_t/os_ext.rs
pub mod os_ext {
use vstd::prelude::*;
use crate::{Core, MemRegion};

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



// File: impl_u/indexing.rs
	#[verifier::external_body]
pub proof fn lemma_entry_base_from_index(base: nat, idx: nat, entry_size: nat)
    requires
        0 < entry_size,
    ensures
        entry_base_from_index(base, idx, entry_size) < next_entry_base_from_index(base, idx, entry_size),
        forall|idx2: nat|
            #![trigger entry_base_from_index(base, idx, entry_size), entry_base_from_index(base, idx2, entry_size)]
            idx < idx2 ==> entry_base_from_index(base, idx, entry_size) < entry_base_from_index(base, idx2, entry_size),
                   // // && next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(layer, base, j),
        // TODO: The line above can't be a separate postcondition because it doesn't have any valid triggers.
        // The trigger for it is pretty bad.
        forall|idx2: nat| idx < idx2
            ==> next_entry_base_from_index(base, idx, entry_size) <= entry_base_from_index(base, idx2, entry_size),
        next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx + 1, entry_size),
        next_entry_base_from_index(base, idx, entry_size) == entry_base_from_index(base, idx, entry_size) + entry_size,
        next_entry_base_from_index(base, idx, entry_size) == entry_size + entry_base_from_index(base, idx, entry_size),
        forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(entry_base_from_index(base, idx, entry_size), n),
        forall|n: nat|
            0 < n && aligned(base, n) && aligned(entry_size, n) ==> #[trigger] aligned(next_entry_base_from_index(base, idx, entry_size), n),
        aligned(base, entry_size) ==> aligned(entry_base_from_index(base, idx, entry_size), entry_size),
        base <= entry_base_from_index(base, idx, entry_size),
	{
		unimplemented!()
	}


}
