use vstd::prelude::*;

fn main() {}

verus!{

// File: src/bitcoin/varint.rs
pub exec static EMPTY_SLICE: &'static [u8]
    ensures
        EMPTY_SLICE@ == Seq::<u8>::empty(),
{
    &[]
}


}
