use vstd::prelude::*;

fn main() {}

verus!{

// File: spec_t/mmu/defs.rs
pub open spec fn new_seq<T>(i: nat, e: T) -> Seq<T>
    decreases i,
{
    if i == 0 {
        seq![]
    } else {
        new_seq((i - 1) as nat, e).push(e)
    }
}


// File: definitions_u.rs
pub proof fn lemma_new_seq<T>(i: nat, e: T)
    ensures
        new_seq(i, e).len() == i,
        forall|j: nat| j < i ==> new_seq(i, e).index(j as int) === e,
{
}


}
