use vstd::prelude::*;
use vstd::assert_by_contradiction;

fn main() {}

verus!{

global size_of usize == 8;

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

	#[verifier::external_body]
    pub open spec fn view(self) -> Map<usize,PTE> {
		unimplemented!()
	}


	#[verifier::external_body]
    pub proof fn lemma_write_seq_push(self, writes: Seq<(usize, usize)>, addr: usize, value: usize)
        ensures
            self.write_seq(writes.push((addr, value)))
                == (PTMem {
                    pml4: self.pml4,
                    mem: self.write_seq(writes).mem.insert(addr, value),
                }),
        decreases writes.len()
	{
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

    pub open spec fn writer_sbuf_subset_tso_writes(self) -> bool {
        forall|a| self.writer_sbuf().contains_fst(a) ==> #[trigger] self.writes.tso.contains(a)
    }

    pub open spec fn inv_sbuf_facts(self, c: Constants) -> bool {
        &&& self.non_writer_sbufs_are_empty(c)
        &&& self.writer_sbuf_entries_are_unique()
        &&& self.writer_sbuf_subset_tso_writes()
    }

}


proof fn lemma_mem_view_after_step_write(pre: State, post: State, c: Constants, lbl: Lbl)
    requires
        pre.happy,
        post.happy,
        pre.wf(c),
        pre.inv_sbuf_facts(c),
        step_WriteNonneg(pre, post, c, lbl) || step_WriteNonpos(pre, post, c, lbl),
    ensures
        post.writer_mem().pml4 == pre.pt_mem.pml4,
        post.writer_mem().mem  == pre.writer_mem().mem.insert(lbl->Write_1, lbl->Write_2),
{
    let (core, wraddr, value) =
        if let Lbl::Write(core, addr, value) = lbl {
            (core, addr, value)
        } else { arbitrary() };
    reveal_with_fuel(vstd::seq::Seq::fold_left, 5);
    if post.writes.core == pre.writes.core {
        pre.pt_mem.lemma_write_seq_push(pre.writer_sbuf(), wraddr, value);
    } else {
        assert_by_contradiction!(pre.writer_sbuf() =~= seq![], {
            assert(pre.writes.tso.contains(pre.writer_sbuf()[0].0));
        });
    }
}
}
