use vstd::prelude::*;
verus! {

#[verifier::auto_ext_equal(assert, assert_by, ensures)]
pub proof fn lemma_auto_smaller_range_of_seq_is_subrange(mem1: Seq<u8>)
    ensures
        forall|i: int, j, k: int, l: int|
            0 <= i <= k <= l <= j <= mem1.len() ==> mem1.subrange(i, j).subrange(k - i, l - i)
                == mem1.subrange(k, l),
{
}

fn main() {
}

} // verus!
