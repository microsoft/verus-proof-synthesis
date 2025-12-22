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

    pub broadcast proof fn lemma_write_seq_first(m: PTMem, writes: Seq<(usize, usize)>)
        requires writes.len() > 0,
        ensures m.write_seq(writes) == #[trigger] m.write(writes[0].0, writes[0].1).write_seq(writes.drop_first())
    {
        let f = |acc: PTMem, wr: (_, _)| acc.write(wr.0, wr.1);
        let new_m = m.write(writes[0].0, writes[0].1);
        writes.lemma_fold_left_alt(m, f);
        writes.subrange(1, writes.len() as int).lemma_fold_left_alt(new_m, f);
    }

}



}
