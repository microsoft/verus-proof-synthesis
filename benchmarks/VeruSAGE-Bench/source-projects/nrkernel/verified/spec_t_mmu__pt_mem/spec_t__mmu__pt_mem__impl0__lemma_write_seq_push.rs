use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/pt_mem.rs
#[verifier::external_body]
proof fn lemma_fold_left_push<A,B>(s: Seq<A>, a: A, b: B, f: spec_fn(B, A) -> B)
    ensures s.push(a).fold_left(b, f) == f(s.fold_left(b, f), a)
{
		unimplemented!()
}

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
    pub broadcast proof fn lemma_write_seq(self, writes: Seq<(usize, usize)>)
        ensures #![trigger self.write_seq(writes)]
            self.write_seq(writes).pml4 == self.pml4,
            self.mem.dom().subset_of(self.write_seq(writes).mem.dom()),
        decreases writes.len()
    {
	unimplemented!()
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
        broadcast use PTMem::lemma_write_seq;
        lemma_fold_left_push(writes, (addr, value), self, |acc: PTMem, wr: (_, _)| acc.write(wr.0, wr.1));
    }

}

}
