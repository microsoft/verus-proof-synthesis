use vstd::prelude::*;

fn main() {}

verus! {

#[allow(unused_macros)]
macro_rules! is_bit_set {
    ($a:expr, $b:expr) => {
        $a & (1u64 << $b) == (1u64 << $b)
    }
}

proof fn lemma_obtain_bit_index_1_aux(a: u64, hi: u64) -> (i: u64)
    requires
        a != 0,
        hi <= 64,
        a >> hi == 0,
    ensures
        i < hi,
        is_bit_set!(a, i),
    decreases hi
{
    assert(hi != 0) by (bit_vector)
        requires a != 0, hi <= 64, a >> hi == 0;
    assert(1u64 << 0 == 1) by (bit_vector);
    if a & 1 == 1 {
        return 0;
    } else {
        assert((a >> 1) != 0 && (a >> 1) >> sub(hi, 1) == 0) by (bit_vector)
            requires a & 1 != 1, a != 0, a >> hi == 0;
        let j = lemma_obtain_bit_index_1_aux(a >> 1, sub(hi, 1));
        assert(is_bit_set!(a, add(j, 1))) by (bit_vector)
            requires is_bit_set!(a >> 1u64, j) && j < 64;
        add(j, 1)
    }
}

}
