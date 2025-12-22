use vstd::prelude::*;


verus! {
    pub fn main()
    {
    }

    pub proof fn lemma_establish_subrange_equivalence(
        mem1: Seq<u8>,
        mem2: Seq<u8>,
    )
        ensures
            forall |i: int, j: int| mem1.subrange(i, j) =~= mem2.subrange(i, j) ==>
                #[trigger] mem1.subrange(i, j) == #[trigger] mem2.subrange(i, j)
    {
    }

}
