use vstd::prelude::*;

verus! {

fn main() {
}

pub proof fn lemma_auto_smaller_range_of_seq_is_subrange(mem1: Seq<u8>)
    ensures
        forall|i: int, j, k: int, l: int|
            0 <= i <= k <= l <= j <= mem1.len() ==> mem1.subrange(i, j).subrange(k - i, l - i)
                == mem1.subrange(k, l),
{
    assert forall|i: int, j, k: int, l: int|
        0 <= i <= k <= l <= j <= mem1.len() implies mem1.subrange(i, j).subrange(k - i, l - i)
        == mem1.subrange(k, l) by {
        assert(mem1.subrange(k, l) == mem1.subrange(i + k - i, i + l - i));
        assert(mem1.subrange(i, j).subrange(k - i, l - i) == mem1.subrange(i + k - i, i + l - i));

    }
}

} // verus!
