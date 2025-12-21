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

    pub proof fn lemma_write_seq_read(self, writes: Seq<(usize, usize)>, i: int)
        requires
            0 <= i < writes.len(),
            forall|j| #![auto] 0 <= j < writes.len() && writes[j].0 == writes[i].0 ==> i == j,
        ensures
            self.write_seq(writes).mem[writes[i].0] == writes[i].1
        decreases writes.len()
    {
        if writes.len() == 0 {
        } else {
            if i == writes.len() - 1 {
            } else {
                self.lemma_write_seq_read(writes.drop_last(), i);
            }
        }
    }

}



}
