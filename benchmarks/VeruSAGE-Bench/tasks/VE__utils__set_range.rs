use vstd::prelude::*;
use vstd::slice::slice_index_get;

fn main() {}

verus!{

// File: src/utils.rs
/// Helper function to splice a sequence of bytes into another sequence of bytes.
pub open spec fn seq_splice(data: Seq<u8>, pos: usize, v: Seq<u8>) -> Seq<u8>
    recommends
        pos + v.len() <= data.len(),
{
    data.take(pos as int) + v + data.skip(pos + v.len() as int)
}

/// Helper function to set a range of bytes in a vector.
pub fn set_range<'a>(data: &mut Vec<u8>, i: usize, input: &[u8])
    requires
        0 <= i + input@.len() <= old(data)@.len() <= usize::MAX,
    ensures
        data@.len() == old(data)@.len()
        && data@ == seq_splice(old(data)@, i, input@),
{
    // data[i..i + input.len()].copy_from_slice(input);
    let mut j = 0;
    while j < input.len()
    {
        data.set(i + j, *slice_index_get(input, j));
        j = j + 1;
    }
}


}
