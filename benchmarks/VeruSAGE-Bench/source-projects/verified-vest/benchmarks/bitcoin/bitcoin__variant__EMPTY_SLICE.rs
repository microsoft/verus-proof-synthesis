use vstd::prelude::*;

fn main() {}

verus!{

// File: src/bitcoin/varint.rs
#[verifier::spinoff_prover]
pub exec static EMPTY_SLICE: &'static [u8]
    ensures
        EMPTY_SLICE@ == Seq::<u8>::empty(),
{
    assert(<_ as View>::view(&[]) =~= Seq::<u8>::empty());
    &[]
}


}
