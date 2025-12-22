use vstd::prelude::*;
use crate::defs::*;
use crate::theorem::RLbl;

fn main() {}

verus!{

// File: spec_t/mmu/rl1.rs
global size_of usize == 8;

// File: spec_t/mmu/rl1.rs
pub mod rl1 {
use vstd::prelude::*;
use crate::{PTE, PTMem , rl3::Writes, Polarity, Core, aligned, Constants, Lbl, MASK_NEG_DIRTY_ACCESS, MAX_BASE, LoadResult, MemOp, update_range};

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

pub enum Step {
    // Mixed
    Invlpg,
    // Faulting memory op due to failed translation
    // (atomic walk)
    MemOpNoTr,
    // Faulting memory op due to failed translation
    // (non-atomic walk result)
    MemOpNoTrNA { vbase: usize },
    // Memory op using a translation from the TLB
    MemOpTLB { tlb_va: usize },
    TLBFill { core: Core, vaddr: usize },
    TLBEvict { core: Core, tlb_va: usize },
    // Non-atomic TLB fill after an unmap
    TLBFillNA { core: Core, vaddr: usize },
    // TSO
    WriteNonneg,
    WriteNonpos,
    Read,
    Barrier,
    SadWrite,
    Sadness,
    Stutter,
}

impl State {

    pub open spec fn is_happy_writenonneg(self, core: Core, addr: usize, value: usize) -> bool {
        &&& !self.writes.tso.is_empty() ==> core == self.writes.core
        &&& self.pt_mem.is_nonneg_write(addr, value)
    }

    pub open spec fn is_happy_writenonpos(self, core: Core, addr: usize, value: usize) -> bool {
        &&& !self.writes.tso.is_empty() ==> core == self.writes.core
        &&& self.pt_mem.is_nonpos_write(addr, value)
    }

    pub open spec fn is_tso_read_deterministic(self, core: Core, addr: usize) -> bool {
        self.writes.tso.contains(addr) ==> self.writes.core == core
    }

    pub open spec fn can_flip_polarity(self, c: Constants) -> bool {
        &&& self.writes.tso === set![]
        &&& self.writes.nonpos === set![]
    }

}


// ---- Mixed (relevant to multiple of TSO/Cache/Non-Atomic) ----

pub open spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Invlpg(core, va)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& !pre.tlbs[core].contains_key(va)

    &&& post == State {
        writes: Writes {
            core: pre.writes.core,
            tso: if core == pre.writes.core { set![] } else { pre.writes.tso },
            nonpos:
                if post.writes.tso === set![] {
                    pre.writes.nonpos.remove(core)
                } else { pre.writes.nonpos },
        },
        pending_maps: if core == pre.writes.core { map![] } else { pre.pending_maps },
        pending_unmaps: if post.writes.nonpos === set![] { map![] } else { pre.pending_unmaps },
        ..pre
    }
}

pub open spec fn step_MemOpNoTr(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy

    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.pt_mem.pt_walk(memop_vaddr).result() is Invalid
    &&& memop.is_pagefault()

    &&& post == pre
}

pub open spec fn step_MemOpNoTrNA(pre: State, post: State, c: Constants, vbase: usize, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::MemOp(core, memop_vaddr, memop)
    &&& pre.happy
    &&& pre.polarity is Mapping

    &&& c.valid_core(core)
    &&& aligned(memop_vaddr as nat, memop.op_size())
    &&& memop.valid_op_size()
    &&& pre.pending_maps.contains_key(vbase)
    &&& vbase <= memop_vaddr < vbase + pre.pending_maps[vbase].frame.size
    &&& memop.is_pagefault()

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
    &&& post.writes == pre.writes
    &&& post.pending_maps == pre.pending_maps
    &&& post.pending_unmaps == pre.pending_unmaps
}

// ---- Non-atomic page table walks ----

/// A TLB fill resulting from an atomic page table walk

pub open spec fn step_TLBFill(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& pre.happy

    &&& c.valid_core(core)
    &&& vaddr < MAX_BASE
    &&& pre.pt_mem.pt_walk(vaddr).result() matches crate::WalkResult::Valid { vbase, pte }

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

/// A TLB fill resulting from a non-atomic page table walk
pub open spec fn step_TLBFillNA(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
    let pte = pre.pending_unmaps[vaddr];
    &&& lbl is Tau
    &&& pre.happy
    &&& pre.polarity is Unmapping

    &&& c.valid_core(core)
    &&& pre.writes.nonpos.contains(core)
    &&& pre.pending_unmaps.contains_key(vaddr)

    &&& post == State {
        tlbs: pre.tlbs.insert(core, pre.tlbs[core].insert(vaddr, pte)),
        ..pre
    }
}

// ---- TSO ----

pub open spec fn step_WriteNonneg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.is_happy_writenonneg(core, addr, value)
    &&& pre.polarity is Mapping || pre.can_flip_polarity(c)

    &&& post.happy      == pre.happy
    &&& post.phys_mem   == pre.phys_mem
    &&& post.pt_mem     == pre.pt_mem.write(addr, value)
    &&& post.tlbs       == pre.tlbs
    &&& post.writes.tso == pre.writes.tso.insert(addr)
    &&& post.writes.core == core
    &&& post.polarity == Polarity::Mapping
    &&& post.writes.nonpos == pre.writes.nonpos
    &&& post.pending_maps == pre.pending_maps.union_prefer_right(
        Map::new(
            |vbase| post.pt_mem@.contains_key(vbase) && !pre.pt_mem@.contains_key(vbase),
            |vbase| post.pt_mem@[vbase]
        ))
    &&& post.pending_unmaps == pre.pending_unmaps
}

pub open spec fn step_WriteNonpos(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Write(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.is_happy_writenonpos(core, addr, value)
    &&& pre.polarity is Unmapping || pre.can_flip_polarity(c)

    &&& post.happy      == pre.happy
    &&& post.phys_mem   == pre.phys_mem
    &&& post.pt_mem     == pre.pt_mem.write(addr, value)
    &&& post.tlbs       == pre.tlbs
    &&& post.writes.tso == pre.writes.tso.insert(addr)
    &&& post.writes.core == core
    &&& post.polarity == Polarity::Unmapping
    &&& post.writes.nonpos == Set::new(|core| c.valid_core(core))
    &&& post.pending_maps == pre.pending_maps
    &&& post.pending_unmaps == pre.pending_unmaps.union_prefer_right(
        Map::new(
            |vbase| pre.pt_mem@.contains_key(vbase) && !post.pt_mem@.contains_key(vbase),
            |vbase| pre.pt_mem@[vbase]
        ))
}

pub open spec fn step_Read(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Read(core, addr, value)

    &&& pre.happy
    &&& c.valid_core(core)
    &&& c.in_ptmem_range(addr as nat, 8)
    &&& aligned(addr as nat, 8)
    &&& pre.is_tso_read_deterministic(core, addr)
            ==> value & MASK_NEG_DIRTY_ACCESS == pre.pt_mem.read(addr) & MASK_NEG_DIRTY_ACCESS

    &&& post == pre
}

pub open spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Barrier(core)

    &&& pre.happy
    &&& c.valid_core(core)

    &&& post == State {
        writes: Writes {
            tso: if core == pre.writes.core { set![] } else { pre.writes.tso },
            ..pre.writes
        },
        pending_maps: if core == pre.writes.core { map![] } else { pre.pending_maps },
        ..pre
    }
}

pub open spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl is Tau
    &&& post == pre
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

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::Invlpg                    => step_Invlpg(pre, post, c, lbl),
        Step::MemOpNoTr                 => step_MemOpNoTr(pre, post, c, lbl),
        Step::MemOpNoTrNA { vbase }     => step_MemOpNoTrNA(pre, post, c, vbase, lbl),
        Step::MemOpTLB { tlb_va }       => step_MemOpTLB(pre, post, c, tlb_va, lbl),
        Step::TLBFill { core, vaddr }   => step_TLBFill(pre, post, c, core, vaddr, lbl),
        Step::TLBEvict { core, tlb_va } => step_TLBEvict(pre, post, c, core, tlb_va, lbl),
        Step::TLBFillNA { core, vaddr } => step_TLBFillNA(pre, post, c, core, vaddr, lbl),
        Step::WriteNonneg               => step_WriteNonneg(pre, post, c, lbl),
        Step::WriteNonpos               => step_WriteNonpos(pre, post, c, lbl),
        Step::Read                      => step_Read(pre, post, c, lbl),
        Step::Barrier                   => step_Barrier(pre, post, c, lbl),
        Step::SadWrite                  => step_SadWrite(pre, post, c, lbl),
        Step::Sadness                   => step_Sadness(pre, post, c, lbl),
        Step::Stutter                   => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}
}

// File: spec_t/mmu/rl2.rs
pub mod rl2 {

use vstd::prelude::*;
use crate::{PTMem, PTE, Walk, Polarity, Constants, MAX_BASE, aligned, Core , rl3::Writes};
use crate::SeqTupExt;

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

    pub open spec fn pending_map_for(self, va: usize) -> bool {
        exists|vb| {
        &&& #[trigger] self.hist.pending_maps.contains_key(vb)
        &&& vb <= va < vb + self.hist.pending_maps[vb].frame.size
        }
    }

}

// Invariants for this state machine

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

    pub open spec fn writer_sbuf_entries_have_P_bit_1(self) -> bool {
        forall|i| #![auto] 0 <= i < self.writer_sbuf().len() ==> self.writer_sbuf()[i].1 & 1 == 1
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

	#[verifier::external_body]
    pub open spec fn inv_unmapping__core_vs_writer_reads(self, c: Constants) -> bool {
		unimplemented!()
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
                     walk_na.result() matches crate::WalkResult::Valid { vbase, pte }
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

	#[verifier::external_body]
    pub open spec fn inv_unmapping__notin_nonpos(self, c: Constants) -> bool {
		unimplemented!()
	}


    pub open spec fn inv_mapping__inflight_walks(self, c: Constants) -> bool {
        forall|core, walk| c.valid_core(core) && #[trigger] self.walks[core].contains(walk) ==> {
            &&& walk.vaddr < MAX_BASE
            &&& aligned(walk.vaddr as nat, 8)
            &&& walk.path.len() <= 3
            &&& !walk.complete
            &&& is_iter_walk_prefix(self.core_mem(core), walk)
        }
    }

    pub open spec fn inv_mapping__valid_is_not_in_sbuf(self, c: Constants) -> bool {
        forall|core, addr: usize|
            c.valid_core(core) && aligned(addr as nat, 8) &&
            core != self.writes.core &&
            #[trigger] self.core_mem(core).read(addr) & 1 == 1
                ==> !self.writer_sbuf().contains_fst(addr)
    }

    pub open spec fn inv_mapping__valid_not_pending_is_not_in_sbuf(self, c: Constants) -> bool {
        forall|va:usize,a|
            #![trigger self.writer_mem().pt_walk(va), self.writer_sbuf().contains_fst(a)]
        {
            let walk = self.writer_mem().pt_walk(va);
            va < MAX_BASE && walk.result() is Valid && !self.pending_map_for(va) && walk.path.contains_fst(a)
                ==> !self.writer_sbuf().contains_fst(a)
        }
    }

    pub open spec fn inv_mapping__pending_map_is_base_walk(self, c: Constants) -> bool {
        forall|va| #![auto] self.hist.pending_maps.contains_key(va) ==> self.writer_mem().is_base_pt_walk(va)
    }

    pub open spec fn inv_mapping(self, c: Constants) -> bool {
        &&& self.writer_sbuf_entries_have_P_bit_1()
        &&& self.inv_mapping__valid_is_not_in_sbuf(c)
        &&& self.inv_mapping__valid_not_pending_is_not_in_sbuf(c)
        &&& self.inv_mapping__inflight_walks(c)
        &&& self.inv_mapping__pending_map_is_base_walk(c)
        &&& self.hist.pending_unmaps === map![]
        &&& self.writes.tso === set![] ==> self.hist.pending_maps === map![]
    }

    pub open spec fn inv_unmapping(self, c: Constants) -> bool {
        &&& self.writes.tso !== set![] ==> self.writes.nonpos === Set::new(|core| c.valid_core(core))
        &&& self.writer_sbuf_entries_have_P_bit_0()
        &&& self.inv_unmapping__inflight_walks(c)
        &&& self.inv_unmapping__core_vs_writer_reads(c)
        &&& self.inv_unmapping__valid_walk(c)
        &&& self.inv_unmapping__notin_nonpos(c)
        &&& self.hist.pending_maps === map![]
        &&& self.writes.nonpos === set![] ==> self.hist.pending_unmaps === map![]
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        self.happy ==> {
        &&& self.wf(c)
        &&& self.inv_sbuf_facts(c)
        &&& self.polarity is Mapping ==> self.inv_mapping(c)
        &&& self.polarity is Unmapping ==> self.inv_unmapping(c)
        }
    }

}


	#[verifier::external_body]
pub open spec fn walk_next(mem: PTMem, walk: Walk) -> Walk {
		unimplemented!()
	}

// MB: Ideally this would be some one liner `walk.path.is_prefix_of(..)`. But that doesn't seem to work well.
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
        let walk = crate::rl2::walk_next(mem, walk);
        if walk.complete { walk } else {
            let walk = crate::rl2::walk_next(mem, walk);
            if walk.complete { walk } else {
                let walk = crate::rl2::walk_next(mem, walk);
                if walk.complete { walk } else {
                    crate::rl2::walk_next(mem, walk)
                }
            }
        }
    }
}

pub mod refinement{

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
pub mod rl3 {
use vstd::prelude::*;
use crate::{PTE, Walk, PTMem, Constants, Core, Lbl};

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

/// Any transition that reads from page table memory takes an arbitrary usize `r`, which is used to
/// non-deterministically flip the accessed and dirty bits.
/// A seemingly easier way to specify this would be:
/// `result & MASK_NEG_DIRTY_ACCESS = read(addr) & MASK_NEG_DIRTY_ACCESS`
/// But this makes specifying the page table walks very awkward because read is now specified as a
/// predicate. Instead we explicitly xor with an arbitrary value. At higher refinement layers we do
/// use the predicate approach because we can prove in the refinement that the value of `r` is
/// irrelevant for page table walks, so the read predicate only shows up in `step_Read`.
pub enum Step {
    Invlpg,
    // Faulting memory op due to failed translation
    MemOpNoTr { walk: Walk, r: usize },
    // Memory op using a translation from the TLB
    MemOpTLB { tlb_va: usize },
    // Translation caching
    CacheFill { core: Core, walk: Walk },
    CacheUse { core: Core, walk: Walk },
    CacheEvict { core: Core, walk: Walk },
    // Non-atomic page table walks
    WalkInit { core: Core, vaddr: usize },
    WalkStep { core: Core, walk: Walk, r: usize },
    WalkAbort { core: Core, walk: Walk },
    TLBFill { core: Core, walk: Walk, r: usize },
    TLBEvict { core: Core, tlb_va: usize },
    // TSO, operations on page table memory
    Write,
    Writeback { core: Core },
    Read { r: usize },
    Barrier,
    Stutter,
}

// State machine transitions

	#[verifier::external_body]
pub closed spec fn step_Invlpg(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn step_MemOpNoTr(
    pre: State,
    post: State,
    c: Constants,
    walk: Walk,
    r: usize,
    lbl: Lbl,
) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn step_MemOpTLB(
    pre: State,
    post: State,
    c: Constants,
    tlb_va: usize,
    lbl: Lbl,
) -> bool {
		unimplemented!()
	}

// ---- Translation caching ----

	#[verifier::external_body]
pub closed spec fn step_CacheFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn step_CacheUse(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn step_CacheEvict(pre: State, post: State, c: Constants, core: Core, walk: Walk, lbl: Lbl) -> bool {
		unimplemented!()
	}

// ---- Non-atomic page table walks ----

	#[verifier::external_body]
pub closed spec fn step_WalkInit(pre: State, post: State, c: Constants, core: Core, vaddr: usize, lbl: Lbl) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn step_WalkStep(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    r: usize,
    lbl: Lbl
    ) -> bool
	{
		unimplemented!()
	}

	#[verifier::external_body]
pub closed spec fn step_WalkAbort(
    pre: State,
    post: State,
    c: Constants,
    core: Core,
    walk: Walk,
    lbl: Lbl
    ) -> bool
	{
		unimplemented!()
	}

/// Completes a (valid) page table walk and caches the resulting translation in the TLB.
///
/// Note: A valid walk's result is a region whose base and size depend on the path taken. E.g. a
/// huge page mapping results in a 2M-sized region. Invalid walks are always for a 4K-sized region.
	#[verifier::external_body]
pub closed spec fn step_TLBFill(pre: State, post: State, c: Constants, core: Core, walk: Walk, r: usize, lbl: Lbl) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn step_TLBEvict(pre: State, post: State, c: Constants, core: Core, tlb_va: usize, lbl: Lbl) -> bool {
		unimplemented!()
	}

// ---- TSO ----
// Our modeling of TSO with store buffers is adapted from the one in the paper "A Better x86 Memory
// Model: x86-TSO".
/// Write to core's local store buffer.
	#[verifier::external_body]
pub closed spec fn step_Write(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn step_Writeback(pre: State, post: State, c: Constants, core: Core, lbl: Lbl) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn step_Read(pre: State, post: State, c: Constants, r: usize, lbl: Lbl) -> bool {
		unimplemented!()
	}

/// The `step_Barrier` transition corresponds to any serializing instruction. This includes
/// `mfence` and `iret`.

	#[verifier::external_body]
pub closed spec fn step_Barrier(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
		unimplemented!()
	}


	#[verifier::external_body]
pub closed spec fn step_Stutter(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
		unimplemented!()
	}


pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        //Step::ReadWrite { paddr, wr }    => step_ReadWrite(pre, post, c, paddr, wr, lbl),
        Step::Invlpg                       => step_Invlpg(pre, post, c, lbl),
        Step::MemOpNoTr { walk, r }        => step_MemOpNoTr(pre, post, c, walk, r, lbl),
        Step::MemOpTLB { tlb_va }          => step_MemOpTLB(pre, post, c, tlb_va, lbl),
        Step::CacheFill { core, walk }     => step_CacheFill(pre, post, c, core, walk, lbl),
        Step::CacheUse { core, walk }      => step_CacheUse(pre, post, c, core, walk, lbl),
        Step::CacheEvict { core, walk }    => step_CacheEvict(pre, post, c, core, walk, lbl),
        Step::WalkInit { core, vaddr }     => step_WalkInit(pre, post, c, core, vaddr, lbl),
        Step::WalkStep { core, walk, r }   => step_WalkStep(pre, post, c, core, walk, r, lbl),
        Step::WalkAbort { core, walk }     => step_WalkAbort(pre, post, c, core, walk, lbl),
        Step::TLBFill { core, walk, r }    => step_TLBFill(pre, post, c, core, walk, r, lbl),
        Step::TLBEvict { core, tlb_va }    => step_TLBEvict(pre, post, c, core, tlb_va, lbl),
        //Step::WalkDone { core, walk, r } => step_WalkDone(pre, post, c, core, walk, r, lbl),
        Step::Write                        => step_Write(pre, post, c, lbl),
        Step::Writeback { core }           => step_Writeback(pre, post, c, core, lbl),
        Step::Read { r }                   => step_Read(pre, post, c, r, lbl),
        Step::Barrier                      => step_Barrier(pre, post, c, lbl),
        Step::Stutter                      => step_Stutter(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}

// Invariants for this state machine

impl State {

	#[verifier::external_body]
    pub closed spec fn inv(self, c: Constants) -> bool {
		unimplemented!()
	}


}

pub mod refinement {

    impl crate::rl3::State {

	#[verifier::external_body]
        pub closed spec fn interp(self) -> crate::rl2::State {
		unimplemented!()
	}
    }

    pub mod to_rl1{
        //! Machinery to lift rl3 semantics to rl1 (interp twice and corresponding lemmas), which we use for
        //! reasoning about the OS state machine.

        use crate::{Lbl, Constants};

        impl crate::rl3::State {

            pub open spec fn view(self) -> crate::rl1::State {
                self.interp().interp()
            }

        }

	#[verifier::external_body]
        pub broadcast proof fn next_preserves_inv(pre: crate::rl3::State, post: crate::rl3::State, c: Constants, lbl: Lbl)
            requires
                pre.inv(c),
                pre.interp().inv(c),
                #[trigger] crate::rl3::next(pre, post, c, lbl),
            ensures
                post.inv(c),
                post.interp().inv(c),
	{
		unimplemented!()
	}

	#[verifier::external_body]
        pub broadcast proof fn next_refines(pre: crate::rl3::State, post: crate::rl3::State, c: Constants, lbl: Lbl)
            requires
                pre.inv(c),
                pre.interp().inv(c),
                #[trigger] crate::rl3::next(pre, post, c, lbl),
            ensures
                crate::rl1::next(pre@, post@, c, lbl),
	{
		unimplemented!()
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

    pub open spec fn is_base_pt_walk(self, vaddr: usize) -> bool {
        &&& vaddr < MAX_BASE
        &&& self.pt_walk(vaddr).result() matches crate::WalkResult::Valid { vbase, pte }
        &&& vbase == vaddr
    }

	#[verifier::external_body]
    pub open spec fn view(self) -> Map<usize,PTE> {
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

// An entry in any page directory (i.e. in PML4, PDPT, PD or PT)
#[repr(transparent)]
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
pub mod defs {
use vstd::prelude::*;

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

pub open spec fn candidate_mapping_overlaps_existing_pmem(mappings: Map<nat, PTE>, pte: PTE) -> bool {
    exists|b: nat| #![auto] {
            &&& mappings.dom().contains(b)
            &&& overlap(pte.frame, mappings.index(b).frame)
        }
}

pub open spec(checked) fn align_to_usize(a: usize, b: usize) -> usize {
    sub(a, a % b)
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

impl MemRegion {

    pub open spec fn contains(self, addr: nat) -> bool {
        between(addr, self.base, self.base + self.size)
    }

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

pub open spec fn update_range<A>(s: Seq<A>, idx: int, new: Seq<A>) -> Seq<A>
{
    s.subrange(0, idx)
      + new
      + s.subrange(idx + new.len(), s.len() as int)
}
}

// File: impl_u/l2_impl.rs
// PDE is defined in crate::spec_t::mmu::defs to define the page table walk
// semantics. Here we reuse it for the implementation and add exec functions to it.
impl PDE {
    // PAT flag is set to zero for huge pages and super pages
    pub open spec fn hp_pat_is_zero(self) -> bool {
        &&& self@ is Page && self.layer == 1 ==> self.entry & MASK_PG_FLAG_PAT == 0
        &&& self@ is Page && self.layer == 2 ==> self.entry & MASK_PG_FLAG_PAT == 0
    }
}

/// PTDir is used in the `ghost_pt` field of the PageTable. It's used to keep track of the memory
/// regions in which the corresponding translation structures are stored.
#[verifier::ext_equal]
pub struct PTDir {
    /// Region of physical memory in which this PTDir is stored
    pub region: MemRegion,
    pub entries: Seq<Option<PTDir>>,
    /// reflexive-transitive closure of `region` over `entries`
    pub used_regions: Set<MemRegion>,
}

// Page table methods are in a separate module for namespacing, since we can't use a struct + impl
// (To use a struct we'd have to keep a &mut reference to the memory in the struct, which Verus
// doesn't support. Or we keep an owned copy but then can't have an external interface that mutably
// borrows a memory.)

pub mod PT {
use super::*;

/// `map_frame_aux` relies on the non-emptiness of directories to determine whether or not
/// mapping a particular addr/page should fail. But during the map/unmap operations we need to
/// recover the invariant to prove the VCs of intermediate transitions, while we do have non-empty
/// directories. Because of that, non-emptiness isn't baked into the invariant directly.
pub open spec(checked) fn inv_and_nonempty(tok: WrappedTokenView, pt: PTDir) -> bool {
    &&& inv(tok, pt)
    // The overall invariant requires that there are no empty directories but this is not part of
    // `inv_at`, so we can still obtain `inv_at` for the whole page table during operations and use
    // it to derive the implementation VCs.
    &&& no_empty_directories(tok, pt, 0, tok.pt_mem.pml4)
}

pub open spec(checked) fn inv(tok: WrappedTokenView, pt: PTDir) -> bool {
    &&& pt.region.base == tok.pt_mem.pml4
    &&& inv_at(tok, pt, 0, tok.pt_mem.pml4)
}

/// Get the view of the entry at address ptr + i * WORD_SIZE
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

pub open spec fn no_empty_directories(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool
    decreases X86_NUM_LAYERS - layer
        when layer_in_range(layer)
{
    forall|i: nat| i < X86_NUM_ENTRIES ==> {
        (#[trigger] entry_at_spec(tok, pt, layer, ptr, i))@ matches GPDE::Directory { addr, ..}
            ==> {
                &&& !empty_at(tok, pt.entries[i as int]->Some_0, layer + 1, addr)
                &&& no_empty_directories(tok, pt.entries[i as int]->Some_0, layer + 1, addr)
            }
    }
}

pub open spec fn empty_at(tok: WrappedTokenView, pt: PTDir, layer: nat, ptr: usize) -> bool {
    forall|i: nat| #![auto] i < X86_NUM_ENTRIES ==> entry_at_spec(tok, pt, layer, ptr, i)@ is Invalid
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

/// Entries for super pages and huge pages use bit 12 to denote the PAT flag. We always set that
/// flag to zero, which allows us to always use the same mask to get the address.
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
}

// File: impl_u/wrapped_token.rs
pub enum OpArgs {
    Map { base: usize, pte: PTE },
    Unmap { base: usize },
}

/// We define a view of the wrapped tokens with the memory stuff that the implementation uses to
/// define its invariant and interpretation. This way read-only ops (e.g. `read`) leave the view
/// fully unchanged, which simplifies reasoning. Otherwise we have to argue that the invariant is
/// preserved as only irrelevant parts of the state may have changed. (Since `read` still has to
/// take a mut ref as it changes the underlying token.)
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

}



// File: spec_t/os.rs
pub mod os {
use vstd::prelude::*;
use crate::theorem::RLbl;
use crate::defs::*;
use crate::os_ext;


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
    pub os_ext: os_ext::State,
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

#[allow(inconsistent_fields)]
pub enum Step {
    MMU,
    MemOp { core: Core },
    ReadPTMem { core: Core, paddr: usize, value: usize },
    Barrier { core: Core },
    Invlpg { core: Core },
    // Map
    MapStart { core: Core },
    MapOpStart { core: Core },
    Allocate { core: Core, res: MemRegion },
    MapOpStutter { core: Core, paddr: usize, value: usize },
    MapOpChange { core: Core, paddr: usize, value: usize },
    MapNoOp { core: Core },
    MapEnd { core: Core },
    // Unmap
    UnmapStart { core: Core },
    UnmapOpStart { core: Core },
    Deallocate { core: Core, reg: MemRegion },
    UnmapOpChange { core: Core, paddr: usize, value: usize },
    UnmapOpStutter { core: Core, paddr: usize, value: usize },
    UnmapOpFail { core: Core },
    UnmapInitiateShootdown { core: Core },
    UnmapWaitShootdown { core: Core },
    AckShootdownIPI { core: Core },
    UnmapEnd { core: Core },
}

impl CoreState {

    pub open spec fn is_mapping(self) -> bool {
        match self {
            CoreState::MapExecuting { .. }
            | CoreState::MapDone { .. } => true,
            _ => false,
        }
    }

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

// Overlapping inflight memory helper functions for HL-soundness
pub open spec fn candidate_mapping_overlaps_inflight_pmem(
    pt: Map<nat, PTE>,
    inflightargs: Set<CoreState>,
    candidate: PTE,
) -> bool {
    exists|b: CoreState| #![auto] {
        &&& inflightargs.contains(b)
        &&& match b {
            CoreState::MapWaiting { vaddr, pte, .. }
            | CoreState::MapExecuting { vaddr, pte, .. }
            | CoreState::MapDone { vaddr, pte, .. } => {
                overlap(candidate.frame, pte.frame)
            },
            CoreState::UnmapWaiting { ult_id, vaddr }
            | CoreState::UnmapExecuting { ult_id, vaddr, result: None, .. } => {
                &&& pt.contains_key(vaddr)
                &&& overlap(candidate.frame, pt[vaddr].frame)
            },
            CoreState::UnmapExecuting { ult_id, vaddr, result: Some(result), .. }
            | CoreState::UnmapOpDone { ult_id, vaddr, result, .. }
            | CoreState::UnmapShootdownWaiting { ult_id, vaddr, result, .. } => {
                &&& result is Ok
                &&& overlap(candidate.frame, result.get_Ok_0().frame)
            },
            CoreState::Idle => false,
        }
    }
}

pub open spec fn inflight_vmem_region(pt: Map<nat, PTE>, core_state: CoreState) -> MemRegion
    recommends !(core_state is Idle)
{
    match core_state {
        CoreState::Idle => arbitrary(),
        CoreState::MapWaiting { vaddr, pte, .. }
        | CoreState::MapExecuting { vaddr, pte, .. }
        | CoreState::MapDone { vaddr, pte, .. } => {
            MemRegion { base: vaddr, size: pte.frame.size }
        }

        CoreState::UnmapWaiting { vaddr, .. }
        | CoreState::UnmapExecuting { vaddr, result: None, .. } => {
            let size = if pt.contains_key(vaddr) { pt[vaddr].frame.size } else { 0 };
            MemRegion { base: vaddr, size: size }
        }

        CoreState::UnmapExecuting { ult_id: ult_id2, vaddr, result: Some(result) }
        | CoreState::UnmapOpDone { ult_id: ult_id2, vaddr, result }
        | CoreState::UnmapShootdownWaiting { ult_id: ult_id2, vaddr, result } => {
            let size = if result is Ok { result.get_Ok_0().frame.size } else { 0 };
            MemRegion { base: vaddr, size: size }
        }
    }
}

pub open spec fn candidate_mapping_overlaps_inflight_vmem(
    pt: Map<nat, PTE>,
    inflightargs: Set<CoreState>,
    base: nat,
    candidate_size: nat,
) -> bool {
    exists|core_state: CoreState| #![auto] {
        &&& inflightargs.contains(core_state)
        &&& !(core_state is Idle)
        &&& overlap(
                inflight_vmem_region(pt, core_state),
                MemRegion { base: base, size: candidate_size },
            )
    }
}

pub open spec fn step_MMU(c: Constants, s1: State, s2: State, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //mmu statemachine steps
    &&& crate::rl3::next(s1.mmu, s2.mmu, c.common, crate::Lbl::Tau)
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_MemOp(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MemOp { thread_id, vaddr, op }
    &&& aligned(vaddr, 8)
    &&& core == c.ult2core[thread_id]
    &&& c.valid_ult(thread_id)
    &&& s1.core_states[core] is Idle
    //mmu statemachine steps
    &&& crate::rl3::next(s1.mmu, s2.mmu, c.common, crate::Lbl::MemOp(core, vaddr as usize, op))
    &&& s2.os_ext == s1.os_ext
    // FIXME(MB): This additional enabling condition here is kind of fishy
    &&& vaddr <= usize::MAX
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

/// Cores can read from page table memory at any point. This transition is used by the
/// implementations of unmap and map to traverse the page table.
pub open spec fn step_ReadPTMem(c: Constants, s1: State, s2: State, core: Core, paddr: usize, value: usize, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //mmu statemachine steps
    &&& crate::rl3::next(s1.mmu, s2.mmu, c.common, crate::Lbl::Read(core, paddr, value))
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

/// Cores can execute a barrier at any point. This transition has to be used after a map.
pub open spec fn step_Barrier(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //mmu statemachine steps
    &&& crate::rl3::next(s1.mmu, s2.mmu, c.common, crate::Lbl::Barrier(core))
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_Invlpg(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    &&& s1.os_ext.shootdown_vec.open_requests.contains(core)
    //mmu statemachine steps
    &&& crate::rl3::next(s1.mmu, s2.mmu, c.common, crate::Lbl::Invlpg(core, s1.os_ext.shootdown_vec.vaddr as usize))
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_Map_sound(
    pt: Map<nat, PTE>,
    inflightargs: Set<CoreState>,
    vaddr: nat,
    pte: PTE,
) -> bool {
    &&& !candidate_mapping_overlaps_existing_pmem(pt, pte)
    &&& !candidate_mapping_overlaps_inflight_pmem(pt, inflightargs, pte)
    &&& !candidate_mapping_overlaps_inflight_vmem(pt, inflightargs, vaddr, pte.frame.size)
}

pub open spec fn step_Map_enabled(c: Constants, vaddr: nat, pte: PTE) -> bool {
    &&& aligned(vaddr, pte.frame.size)
    &&& aligned(pte.frame.base, pte.frame.size)
    &&& candidate_mapping_in_bounds(vaddr, pte)
    &&& candidate_mapping_in_bounds_pmem(c.common, pte)
    &&& {  // The size of the frame must be the entry_size of a layer that supports page mappings
        ||| pte.frame.size == L3_ENTRY_SIZE
        ||| pte.frame.size == L2_ENTRY_SIZE
        ||| pte.frame.size == L1_ENTRY_SIZE
    }
    //&&& pt_mem.alloc_available_pages() >= 3
}

pub open spec fn step_MapStart(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MapStart { thread_id, vaddr, pte }
    &&& core == c.ult2core[thread_id]
    //enabling conditions
    &&& c.valid_ult(thread_id)
    &&& s1.core_states[core] is Idle
    &&& step_Map_enabled(c, vaddr, pte)

    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapWaiting { ult_id: thread_id, vaddr, pte })
    &&& s2.sound == (s1.sound && step_Map_sound(s1.interp_pt_mem(), s1.core_states.values(), vaddr, pte))
}

pub open spec fn step_MapOpStart(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::MapWaiting { ult_id, vaddr, pte }

    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.common, os_ext::Lbl::AcquireLock { core })

    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapExecuting { ult_id, vaddr, pte })
    &&& s2.sound == s1.sound
}

pub open spec fn step_MapOpStutter(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    paddr: usize,
    value: usize,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] is MapExecuting
    &&& value & 1 == 1
    &&& s1.os_ext.is_in_allocated_region(paddr as nat)

    // mmu statemachine steps
    &&& crate::rl3::next(s1.mmu, s2.mmu, c.common, crate::Lbl::Write(core, paddr, value))
    &&& s2.mmu@.happy == s1.mmu@.happy
    &&& s2.interp_pt_mem() == s1.interp_pt_mem()
    &&& s2.os_ext == s1.os_ext

    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

/// Cores can only allocate pages when they are in a map operation.
/// TODO: We'll need to pre-allocate 4 pages before starting a map to avoid failing allocate calls.
pub open spec fn step_Allocate(c: Constants, s1: State, s2: State, core: Core, res: MemRegion, lbl: RLbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& s1.core_states[core] is MapExecuting

    //mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.common, os_ext::Lbl::Allocate { core, res })
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_MapOpChange(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    paddr: usize,
    value: usize,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::MapExecuting { ult_id, vaddr, pte }
    &&& !candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte)
    &&& value & 1 == 1
    &&& s1.os_ext.is_in_allocated_region(paddr as nat)
    &&& s2.interp_pt_mem() == s1.interp_pt_mem().insert(vaddr, pte)

    // mmu statemachine steps
    &&& crate::rl3::next(s1.mmu, s2.mmu, c.common, crate::Lbl::Write(core, paddr, value))
    &&& s2.mmu@.happy == s1.mmu@.happy
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapDone { ult_id, vaddr, pte, result: Ok(()) })
    &&& s1.sound == s2.sound
}

pub open spec fn step_MapNoOp(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::MapExecuting { ult_id, vaddr, pte }
    &&& candidate_mapping_overlaps_existing_vmem(s1.interp_pt_mem(), vaddr, pte)

    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::MapDone { ult_id, vaddr, pte, result: Err(()) })
    &&& s1.sound == s2.sound
}

pub open spec fn step_MapEnd(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::MapEnd { thread_id, vaddr, result }
    // enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::MapDone { ult_id, vaddr: vaddr2, pte, result: result2 }
    &&& thread_id == ult_id && vaddr == vaddr2 && result == result2
    &&& s1.mmu@.writes.tso === set![]
    &&& s1.mmu@.pending_maps === map![]
    &&& s2.inv_impl() // impl invariant is re-established

    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.common, os_ext::Lbl::ReleaseLock { core })

    // new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::Idle)
    &&& s1.sound == s2.sound
}

pub open spec fn step_Unmap_sound(s1: State, vaddr: nat, pte_size: nat) -> bool {
    !candidate_mapping_overlaps_inflight_vmem(s1.interp_pt_mem(), s1.core_states.values(), vaddr, pte_size)
}

pub open spec fn step_Unmap_enabled(vaddr: nat) -> bool {
    &&& vaddr < x86_arch_spec.upper_vaddr(0, 0)
    &&& { // The given vaddr must be aligned to some valid page size
        ||| aligned(vaddr, L3_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L2_ENTRY_SIZE as nat)
        ||| aligned(vaddr, L1_ENTRY_SIZE as nat)
    }
}

pub open spec fn step_UnmapStart(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::UnmapStart { thread_id, vaddr }
    &&& {
    let pt = s1.interp_pt_mem();
    let pte_size = if pt.contains_key(vaddr) { pt[vaddr].frame.size } else { 0 };
    //enabling conditions
    &&& core == c.ult2core[thread_id]
    &&& c.valid_ult(thread_id)
    &&& s1.core_states[core] is Idle
    &&& step_Unmap_enabled(vaddr)
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::UnmapWaiting { ult_id: thread_id, vaddr })
    &&& s2.sound == (s1.sound && step_Unmap_sound(s1, vaddr, pte_size))
    }
}

pub open spec fn step_UnmapOpStart(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::UnmapWaiting { ult_id, vaddr }
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.common, os_ext::Lbl::AcquireLock { core })
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::UnmapExecuting { ult_id, vaddr, result: None })
    &&& s2.sound == s1.sound
}

pub open spec fn step_Deallocate(c: Constants, s1: State, s2: State, core: Core, reg: MemRegion, lbl: RLbl) -> bool {
    &&& lbl is Tau

    &&& c.valid_core(core)
    &&& s1.core_states[core] is UnmapExecuting
    &&& forall|pa: usize|
            aligned(pa as nat, 8) && reg.contains(pa as nat)
                ==> #[trigger] s1.mmu@.pt_mem.read(pa) == 0

    //mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.common, os_ext::Lbl::Deallocate { core, reg })
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapOpChange(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    paddr: usize,
    value: usize,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::UnmapExecuting { ult_id, vaddr, result: None }
    &&& value & 1 == 0
    // mmu statemachine steps
    &&& crate::rl3::next(s1.mmu, s2.mmu, c.common, crate::Lbl::Write(core, paddr, value))
    &&& s2.mmu@.happy == s1.mmu@.happy
    &&& s1.os_ext.is_in_allocated_region(paddr as nat)
    &&& s1.interp_pt_mem().contains_key(vaddr)
    &&& s2.interp_pt_mem() == s1.interp_pt_mem().remove(vaddr)
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapExecuting { ult_id, vaddr, result: Some(Ok(s1.interp_pt_mem()[vaddr])) }
    )

    &&& s2.os_ext == s1.os_ext
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapOpStutter(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    paddr: usize,
    value: usize,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::UnmapExecuting { ult_id, vaddr, result: Some(res) }
    &&& value & 1 == 0
    &&& s1.os_ext.is_in_allocated_region(paddr as nat)
    &&& s2.interp_pt_mem() == s1.interp_pt_mem()
    // mmu statemachine steps
    &&& crate::rl3::next(s1.mmu, s2.mmu, c.common, crate::Lbl::Write(core, paddr, value))
    &&& s2.mmu@.happy == s1.mmu@.happy
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapOpFail(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::UnmapExecuting { ult_id, vaddr, result: None }
    &&& !s1.interp_pt_mem().contains_key(vaddr)
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& s2.os_ext == s1.os_ext
    //new state
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapOpDone { ult_id, vaddr, result: Err(()) }
    )
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapInitiateShootdown(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] matches CoreState::UnmapExecuting { ult_id, vaddr, result: Some(Ok(pte)) }
    &&& s1.mmu@.writes.tso === set![]
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.common, os_ext::Lbl::InitShootdown { core, vaddr })
    //new state
    &&& s2.core_states == s1.core_states.insert(
        core,
        CoreState::UnmapShootdownWaiting { ult_id, vaddr, result: Ok(pte) },
    )
    &&& s2.sound == s1.sound
}

pub open spec fn step_AckShootdownIPI(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::AckShootdownIPI { core: score } && score == core
    //enabling conditions
    &&& c.valid_core(core)
    &&& !s1.mmu@.writes.nonpos.contains(core)
    &&& !s1.mmu@.tlbs[core].contains_key(s1.os_ext.shootdown_vec.vaddr as usize)
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.common, os_ext::Lbl::AckShootdown { core })
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapWaitShootdown(
    c: Constants,
    s1: State,
    s2: State,
    core: Core,
    lbl: RLbl,
) -> bool {
    &&& lbl is Tau
    //enabling conditions
    &&& c.valid_core(core)
    &&& s1.core_states[core] is UnmapShootdownWaiting
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.common, os_ext::Lbl::WaitShootdown { core })
    //new state
    &&& s2.core_states == s1.core_states
    &&& s2.sound == s1.sound
}

pub open spec fn step_UnmapEnd(c: Constants, s1: State, s2: State, core: Core, lbl: RLbl) -> bool {
    &&& lbl matches RLbl::UnmapEnd { thread_id, vaddr, result }
    //enabling conditions
    &&& c.valid_core(core)
    &&& match s1.core_states[core] {
        CoreState::UnmapShootdownWaiting { result: r2, vaddr: v2, ult_id: id2, .. } => {
            &&& result is Ok
            &&& r2 is Ok
            &&& vaddr == v2
            &&& thread_id == id2
            &&& s1.os_ext.shootdown_vec.open_requests.is_empty()
        },
        CoreState::UnmapOpDone { result: r2, vaddr: v2, ult_id: id2, .. } => {
            &&& result is Err
            &&& r2 is Err
            &&& vaddr == v2
            &&& thread_id == id2
        },
        _ => false,
    }
    &&& s2.inv_impl() // impl invariant is re-established
    &&& s1.mmu@.writes.tso === set![]
    &&& s1.mmu@.writes.nonpos === set![]
    &&& s1.mmu@.pending_unmaps === map![]
    // mmu statemachine steps
    &&& s2.mmu == s1.mmu
    &&& os_ext::next(s1.os_ext, s2.os_ext, c.common, os_ext::Lbl::ReleaseLock { core })
    //new state
    &&& s2.core_states == s1.core_states.insert(core, CoreState::Idle)
    &&& s1.sound == s2.sound
}

pub open spec fn next_step(c: Constants, s1: State, s2: State, step: Step, lbl: RLbl) -> bool {
    match step {
        Step::MMU                                   => step_MMU(c, s1, s2, lbl),
        Step::MemOp { core }                        => step_MemOp(c, s1, s2, core, lbl),
        Step::ReadPTMem { core, paddr, value }      => step_ReadPTMem(c, s1, s2, core, paddr, value, lbl),
        Step::Barrier { core }                      => step_Barrier(c, s1, s2, core, lbl),
        Step::Invlpg { core }                       => step_Invlpg(c, s1, s2, core, lbl),
        //Map steps
        Step::MapStart { core }                     => step_MapStart(c, s1, s2, core, lbl),
        Step::MapOpStart { core }                   => step_MapOpStart(c, s1, s2, core, lbl),
        Step::Allocate { core, res }                => step_Allocate(c, s1, s2, core, res, lbl),
        Step::MapOpStutter { core, paddr, value }   => step_MapOpStutter(c, s1, s2, core, paddr, value, lbl),
        Step::MapOpChange { core, paddr, value }    => step_MapOpChange(c, s1, s2, core, paddr, value, lbl),
        Step::MapNoOp { core }                      => step_MapNoOp(c, s1, s2, core, lbl),
        Step::MapEnd { core }                       => step_MapEnd(c, s1, s2, core, lbl),
        //Unmap steps
        Step::UnmapStart { core }                   => step_UnmapStart(c, s1, s2, core, lbl),
        Step::UnmapOpStart { core }                 => step_UnmapOpStart(c, s1, s2, core, lbl),
        Step::Deallocate { core, reg }              => step_Deallocate(c, s1, s2, core, reg, lbl),
        Step::UnmapOpChange { core, paddr, value }  => step_UnmapOpChange(c, s1, s2, core, paddr, value, lbl),
        Step::UnmapOpStutter { core, paddr, value } => step_UnmapOpStutter(c, s1, s2, core, paddr, value, lbl),
        Step::UnmapOpFail { core }                  => step_UnmapOpFail(c, s1, s2, core, lbl),
        Step::UnmapInitiateShootdown { core }       => step_UnmapInitiateShootdown(c, s1, s2, core, lbl),
        Step::UnmapWaitShootdown { core }           => step_UnmapWaitShootdown(c, s1, s2, core, lbl),
        Step::AckShootdownIPI { core }              => step_AckShootdownIPI(c, s1, s2, core, lbl),
        Step::UnmapEnd { core }                     => step_UnmapEnd(c, s1, s2, core, lbl),
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

    pub open spec fn paddr(self, pt: Map<nat, PTE>) -> nat
        recommends self.has_pte(pt),
    {
        match self {
            CoreState::MapWaiting { pte, .. }
            | CoreState::MapExecuting { pte, .. }
            | CoreState::MapDone { pte, .. } => {
                pte.frame.base
            }
            CoreState::UnmapWaiting { vaddr, .. }  
            | CoreState::UnmapExecuting { vaddr, result: None, .. } => pt[vaddr].frame.base,
            | CoreState::UnmapExecuting { result: Some(Ok(pte)), .. }
            | CoreState::UnmapOpDone { result: Ok(pte), .. }
            | CoreState::UnmapShootdownWaiting { result: Ok(pte), .. } => {
               pte.frame.base
            }
            _ => arbitrary(),
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
        nat_keys(self.mmu@.pt_mem@)
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

    pub open spec fn inv_pending_maps(self, c: Constants) -> bool {
        &&& forall |base| #[trigger] self.mmu@.pending_maps.dom().contains(base) ==>
            exists |core| Self::is_pending_for_core(c, base, core,
                self.core_states, self.mmu@.pending_maps)
    }

    pub open spec fn is_pending_for_core(c: Constants, base: usize, core: Core, core_states: Map<Core, CoreState>, pending_maps: Map<usize, PTE>) -> bool
        recommends pending_maps.dom().contains(base)
    {
        core_states.dom().contains(core)
            && match core_states[core] {
                CoreState::MapDone { ult_id, vaddr, pte, result } =>
                    vaddr == base
                     && pte == pending_maps[base],
                _ => false,
            }
    }

    pub open spec fn inv_mmu(self, c: Constants) -> bool {
        &&& self.mmu.inv(c.common)
        // The rl3 invariant is closed, the rl2 one is not but maybe it should be. Keeping it open
        // for now because it accidentally helps with some of the wrapped_token proofs.
        &&& self.mmu.interp().inv(c.common)
        &&& self.mmu@.happy

        // Some of this is duplicated from rl2's invariant but we should close that definition
        // probably.
        &&& self.mmu@.pt_mem.mem.dom() === Set::new(|va| aligned(va as nat, 8) && c.common.in_ptmem_range(va as nat, 8))
        &&& aligned(self.mmu@.pt_mem.pml4 as nat, 4096)
        &&& c.common.in_ptmem_range(self.mmu@.pt_mem.pml4 as nat, 4096)
        &&& c.common.range_mem.0 < c.common.range_mem.1 < c.common.range_ptmem.0 < c.common.range_ptmem.1
        &&& c.common.range_ptmem.1 <= MAX_PHYADDR
        &&& self.mmu@.phys_mem.len() == c.common.range_mem.1
    }

    pub open spec fn inv_allocated_mem(self, c: Constants) -> bool {
        &&& forall|r| #[trigger] self.os_ext.allocated.contains(r) ==> {
            &&& aligned(r.base, 4096)
            &&& c.common.in_ptmem_range(r.base, 4096)
            &&& r.size == 4096
        }
        &&& self.allocated_regions_disjoint()
        &&& self.unallocated_memory_zeroed(c)
    }

    pub open spec fn unallocated_memory_zeroed(self, c: Constants) -> bool {
        forall|pa: usize|
            // aligned(pa as nat, 8) && c.common.in_ptmem_range(pa as nat, 8) &&
            // (forall|r| #[trigger] self.os_ext.allocated.contains(r) ==> !r.contains(pa))
            //     ==> #[trigger] self.mmu@.pt_mem.read(pa) == 0
            //
            // aligned(pa as nat, 8) && c.common.in_ptmem_range(pa as nat, 8) &&
            // !(exists|r| #[trigger] self.os_ext.allocated.contains(r) && r.contains(pa))
            //     ==> #[trigger] self.mmu@.pt_mem.read(pa) == 0
            //
            aligned(pa as nat, 8) && c.common.in_ptmem_range(pa as nat, 8) && #[trigger] self.mmu@.pt_mem.read(pa) != 0
                ==> exists|r| #[trigger] self.os_ext.allocated.contains(r) && r.contains(pa as nat)
    }

    pub open spec fn allocated_regions_disjoint(self) -> bool {
        forall|r1, r2|
            self.os_ext.allocated.contains(r1)
            && self.os_ext.allocated.contains(r2)
            && r1 != r2
            ==> !(#[trigger] overlap(r1, r2))
    }

    pub open spec fn inv_shootdown(self, c: Constants) -> bool {
        &&& !(self.os_ext.lock matches Some(core) && self.core_states[core] is UnmapShootdownWaiting)
            ==> self.os_ext.shootdown_vec.open_requests.is_empty()
        &&& (self.os_ext.lock matches Some(core) &&
            self.core_states[core] matches CoreState::UnmapShootdownWaiting { .. })
            ==> {
                &&& self.mmu@.writes.tso === set![]
                &&& self.mmu@.writes.nonpos.subset_of(self.os_ext.shootdown_vec.open_requests)
            }
    }

    pub open spec fn inv_writes(self, c: Constants) -> bool {
        &&& self.mmu@.writes.nonpos.subset_of(Set::new(|core| c.valid_core(core)))
        &&& (self.os_ext.lock matches Some(core) && self.core_states[core].is_mapping())
                ==> self.mmu@.writes.nonpos === set![]
        &&& (self.os_ext.lock matches Some(core) &&
            self.core_states[core] matches CoreState::UnmapExecuting { result: None, .. })
                ==> self.mmu@.writes.tso === set![] && self.mmu@.writes.nonpos === set![]
        &&& self.os_ext.lock is None ==> {
            &&& self.mmu@.writes.tso === set![]
            &&& self.mmu@.writes.nonpos === set![]
        }
        &&& forall|core|
            #[trigger] c.valid_core(core)
            && self.core_states[core].is_in_crit_sect()
            && self.mmu@.writes.tso !== set![]
                ==> self.mmu@.writes.core == core
    }

    /// This invariant isn't particularly meaningful in the OS state machine. It's trivially
    /// preserved when no thread holds the lock, and its preservation when the lock is held is
    /// ensured by the implementation, via enabling conditions on the corresponding transitions.
    /// The only tricky part is proving it from `init`.
    pub open spec fn inv_impl(self) -> bool {
        self.os_ext.lock is None ==>
            forall|wtok: crate::WrappedTokenView| ({
                &&& wtok.pt_mem == self.mmu@.pt_mem
                &&& wtok.regions.dom() == self.os_ext.allocated
                &&& #[trigger] wtok.regions_derived_from_view()
            }) ==> exists|pt| crate::PT::inv_and_nonempty(wtok, pt)
    }

    pub open spec fn inv(self, c: Constants) -> bool {
        &&& self.inv_basic(c)
        &&& self.inv_mmu(c)
        &&& self.inv_impl()
        &&& self.inv_writes(c)
        &&& self.inv_shootdown(c)
        &&& self.inv_allocated_mem(c)
        &&& self.tlb_inv(c)
        &&& self.overlapping_mem_inv(c)
        &&& self.inv_pending_maps(c)
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

    pub open spec fn inv_unmapped_vmem_no_overlap_existing_vmem(self, c: Constants) -> bool {
        forall|core| #![auto](c.valid_core(core) && self.core_states[core].is_unmapping() 
                    && !(self.core_states[core] is UnmapExecuting && self.core_states[core]->UnmapExecuting_result is None)
                    && !(self.core_states[core] is UnmapOpDone && self.core_states[core]->UnmapOpDone_result is Err)
                    && !(self.core_states[core] is UnmapWaiting))
                ==> !candidate_mapping_overlaps_existing_vmem(
                        self.interp_pt_mem(),
                        self.core_states[core].vaddr(),
                        self.core_states[core].PTE(),
            )
    }

    pub open spec fn inv_existing_map_no_overlap_existing_vmem(self, c: Constants) -> bool {
        forall|vaddr| #[trigger] self.interp_pt_mem().contains_key(vaddr)
                ==> !candidate_mapping_overlaps_existing_vmem(
                        self.interp_pt_mem().remove(vaddr),
                        vaddr,
                        self.interp_pt_mem()[vaddr],
            )
    }

    pub open spec fn inv_inflight_pmem_no_overlap_inflight_pmem(self, c: Constants) -> bool {
        forall|core1: Core, core2: Core|
            (c.valid_core(core1) && c.valid_core(core2)
                //might also need unmaps
                && self.core_states[core1].has_pte(self.interp_pt_mem()) && self.core_states[core2].has_pte(self.interp_pt_mem())
                && overlap(
                MemRegion {
                    base: self.core_states[core1].paddr(self.interp_pt_mem()),
                    size: self.core_states[core1].pte_size(self.interp_pt_mem()),
                },
                MemRegion {
                    base: self.core_states[core2].paddr(self.interp_pt_mem()),
                    size: self.core_states[core2].pte_size(self.interp_pt_mem()),
                },
            )) ==> core1 === core2
    }

    pub open spec fn inv_inflight_pmem_no_overlap_existing_pmem(self, c: Constants) -> bool {
        forall|core| #![auto](c.valid_core(core) && self.core_states[core].has_pte(self.interp_pt_mem())) 
                    && !(self.core_states[core] is MapDone && self.core_states[core]->MapDone_result is Ok)
                    && !(self.core_states[core] is UnmapExecuting && self.core_states[core]->UnmapExecuting_result is None)
                    && !(self.core_states[core] is UnmapWaiting)
                ==> !candidate_mapping_overlaps_existing_pmem(
                        self.interp_pt_mem(),
                        self.core_states[core].PTE(),
            )
    }

    pub open spec fn inv_mapped_pmem_no_overlap(self, c: Constants) -> bool {
        forall|vaddr1, vaddr2|
            (self.interp_pt_mem().contains_key(vaddr1)
                && self.interp_pt_mem().contains_key(vaddr2)
                && overlap(
                    self.interp_pt_mem()[vaddr1].frame,
                    self.interp_pt_mem()[vaddr2].frame)
                ) ==> vaddr1 === vaddr2
    }

    pub open spec fn overlapping_mem_inv(self, c: Constants) -> bool {
        self.sound ==> {
            &&& self.inv_inflight_map_no_overlap_inflight_vmem(c)
            &&& self.inv_unmapped_vmem_no_overlap_existing_vmem(c)
            &&& self.inv_existing_map_no_overlap_existing_vmem(c)
            &&& self.inv_inflight_pmem_no_overlap_inflight_pmem(c)
            &&& self.inv_inflight_pmem_no_overlap_existing_pmem(c)
            &&& self.inv_mapped_pmem_no_overlap(c)
        }
    }

}
}


// File: spec_t/os_ext.rs
pub mod os_ext {
    use vstd::prelude::*;
    use crate::defs::*;
    use crate::Constants;

// describes how the rest of the OS behaves
// This is the "rest of the OS". It specifies the kernel lock, (de-)allocation, and
// shootdown coordination

pub enum Lbl {
    Tau,
    AcquireLock { core: Core },
    ReleaseLock { core: Core },
    InitShootdown { core: Core, vaddr: nat },
    WaitShootdown { core: Core },
    AckShootdown { core: Core },
    Allocate { core: Core, res: MemRegion },
    Deallocate { core: Core, reg: MemRegion },
}

pub struct State {
    pub lock: Option<Core>,
    pub shootdown_vec: ShootdownVector,
    pub allocated: Set<MemRegion>,
}

pub struct ShootdownVector {
    pub vaddr: nat,
    pub open_requests: Set<Core>,
}

impl State {

    pub open spec fn disjoint_from_allocations(self, reg: MemRegion) -> bool {
        forall|reg2| #[trigger] self.allocated.contains(reg2) ==> !overlap(reg, reg2)
    }

    pub open spec fn is_in_allocated_region(self, pa: nat) -> bool {
        exists|r| #[trigger] self.allocated.contains(r) && r.base <= pa < r.base + r.size
    }

}


pub enum Step {
    AcquireLock,
    ReleaseLock,
    InitShootdown,
    WaitShootdown,
    AckShootdown,
    Allocate,
    Deallocate
}

// State machine transitions

pub open spec fn step_AcquireLock(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::AcquireLock { core }

    &&& c.valid_core(core)
    &&& pre.lock is None

    &&& post == State {
        lock: Some(core),
        ..pre
    }
}

pub open spec fn step_ReleaseLock(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::ReleaseLock { core }

    &&& c.valid_core(core)
    &&& pre.lock == Some(core)

    &&& post == State {
        lock: None,
        ..pre
    }
}

// This initiates a shootdown for all other cores in the system, so we don't take the cores as an
// argument.

pub open spec fn step_InitShootdown(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::InitShootdown { core, vaddr }

    &&& c.valid_core(core)
    &&& pre.shootdown_vec.open_requests === set![]

    &&& post == State {
        shootdown_vec: ShootdownVector {
            vaddr,
            open_requests: Set::new(|core| c.valid_core(core))
        },
        ..pre
    }
}

/// Wait until all cores have acknowledged the shootdown request

pub open spec fn step_WaitShootdown(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::WaitShootdown { core }

    &&& c.valid_core(core)
    &&& pre.shootdown_vec.open_requests === set![]

    &&& post == pre
}

pub open spec fn step_AckShootdown(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::AckShootdown { core }

    &&& c.valid_core(core)
    &&& pre.shootdown_vec.open_requests.contains(core)

    &&& post == State {
        shootdown_vec: ShootdownVector {
            open_requests: pre.shootdown_vec.open_requests.remove(core),
            ..pre.shootdown_vec
        },
        ..pre
    }
}

pub open spec fn step_Allocate(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Allocate { core, res }

    &&& c.valid_core(core)
    &&& pre.disjoint_from_allocations(res)
    &&& aligned(res.base, 4096)
    &&& c.in_ptmem_range(res.base, 4096)
    &&& res.size == 4096

    &&& post == State {
        allocated: pre.allocated.insert(res),
        ..pre
    }
}

pub open spec fn step_Deallocate(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    &&& lbl matches Lbl::Deallocate { core, reg }

    &&& c.valid_core(core)
    &&& pre.allocated.contains(reg)

    &&& post == State {
        allocated: pre.allocated.remove(reg),
        ..pre
    }
}

pub open spec fn next_step(pre: State, post: State, c: Constants, step: Step, lbl: Lbl) -> bool {
    match step {
        Step::AcquireLock   => step_AcquireLock(pre, post, c, lbl),
        Step::ReleaseLock   => step_ReleaseLock(pre, post, c, lbl),
        Step::InitShootdown => step_InitShootdown(pre, post, c, lbl),
        Step::WaitShootdown => step_WaitShootdown(pre, post, c, lbl),
        Step::AckShootdown  => step_AckShootdown(pre, post, c, lbl),
        Step::Allocate      => step_Allocate(pre, post, c, lbl),
        Step::Deallocate    => step_Deallocate(pre, post, c, lbl),
    }
}

pub open spec fn next(pre: State, post: State, c: Constants, lbl: Lbl) -> bool {
    exists|step| next_step(pre, post, c, step, lbl)
}
}

// File: spec_t/mmu/mod.rs
// trusted: definitions for the trusted low-level hardware model
// Only used in the simplified hardware models.

pub enum Polarity {
    Mapping,
    Unmapping,
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
            crate::WalkResult::Valid {
                vbase,
                pte: PTE {
                    frame: MemRegion { base: base as nat, size: size as nat },
                    flags: self.flags(),
                }
            }
        } else if path.last().1 is Invalid {
            // The result holds for one page
            crate::WalkResult::Invalid { vaddr: align_to_usize(self.vaddr, PAGE_SIZE) }
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



// File: theorem.rs
pub mod theorem{
use vstd::prelude::*;
use crate::defs::{ MemOp, PTE, Core };


pub enum RLbl {
    Tau,
    MemOp      { thread_id: nat, vaddr: nat, op: MemOp },
    MapStart   { thread_id: nat, vaddr: nat, pte: PTE },
    MapEnd     { thread_id: nat, vaddr: nat, result: Result<(), ()> },
    UnmapStart { thread_id: nat, vaddr: nat },
    UnmapEnd   { thread_id: nat, vaddr: nat, result: Result<(), ()> },
    AckShootdownIPI { core: Core },
}
}

// File: spec_t/os_invariant.rs
#[verifier::rlimit(200)]
pub proof fn next_step_preserves_inv_writes(c: os::Constants, s1: os::State, s2: os::State, step: os::Step, lbl: RLbl)
    requires
        s1.inv(c),
        os::next_step(c, s1, s2, step, lbl),
    ensures
        s2.inv_writes(c),
{
}


}
