use vstd::prelude::*;

fn main() {}

verus!{

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

    pub proof fn lemma_write_seq(self, writes: Seq<(usize, usize)>)
        ensures #![trigger self.write_seq(writes)]
            self.write_seq(writes).pml4 == self.pml4,
            self.mem.dom().subset_of(self.write_seq(writes).mem.dom()),
    {
    }
}



}
