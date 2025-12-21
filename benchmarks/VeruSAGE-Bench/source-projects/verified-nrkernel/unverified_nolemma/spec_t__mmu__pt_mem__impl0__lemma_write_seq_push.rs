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

    pub proof fn lemma_write_seq_push(self, writes: Seq<(usize, usize)>, addr: usize, value: usize)
        ensures
            self.write_seq(writes.push((addr, value)))
                == (PTMem {
                    pml4: self.pml4,
                    mem: self.write_seq(writes).mem.insert(addr, value),
                }),
        decreases writes.len()
    {
    }

}

}
