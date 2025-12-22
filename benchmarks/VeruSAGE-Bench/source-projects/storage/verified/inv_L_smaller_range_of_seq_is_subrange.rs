use vstd::prelude::*;

verus! {

fn main() {
}

pub proof fn lemma_smaller_range_of_seq_is_subrange(mem1: Seq<u8>, i: int, j: int, k: int, l: int)
    requires
        0 <= i <= k <= l <= j <= mem1.len(),
    ensures
        mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(k, l),
{
    assert(mem1.subrange(k, l) == mem1.subrange(i + k - i, i + l - i));
    assert(mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(i + k - i, i + l - i));
}

} // verus!
