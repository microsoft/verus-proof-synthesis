use vstd::prelude::*;
use vstd::slice::slice_index_get;

fn main() {}

verus!{

// File: src/utils.rs
pub open spec fn seq_splice(data: Seq<u8>, pos: usize, v: Seq<u8>) -> Seq<u8>
    recommends
        pos + v.len() <= data.len(),
{
    data.take(pos as int) + v + data.skip(pos + v.len() as int)
}

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
        invariant
            data@.len() == old(data)@.len(),
            forall|k| 0 <= k < i ==> data@[k] == old(data)@[k],
            forall|k| i + input@.len() <= k < data@.len() ==> data@[k] == old(data)@[k],
            0 <= i <= i + j <= i + input@.len() <= data@.len() <= usize::MAX,
            forall|k| 0 <= k < j ==> data@[i + k] == input@[k],
        decreases input@.len() - j,
    {
        data.set(i + j, *slice_index_get(input, j));
        j = j + 1
    }
    assert(data@ =~= old(data)@.subrange(0, i as int).add(input@).add(
        old(data)@.subrange(i + input@.len(), data@.len() as int),
    ))
}


}
