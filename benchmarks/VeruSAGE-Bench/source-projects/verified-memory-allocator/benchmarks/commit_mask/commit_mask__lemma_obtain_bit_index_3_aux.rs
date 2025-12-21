use vstd::prelude::*;

fn main() {}

verus! {

    global size_of usize == 8;

#[allow(unused_macros)]
macro_rules! is_bit_set {
    ($a:expr, $b:expr) => {
        $a & (1u64 << $b) == (1u64 << $b)
    }
}
proof fn lemma_obtain_bit_index_3_aux(a: u64, b: u64, hi: u64) -> (i: u64)
    requires
        a & b != b,
        hi <= 64,
        a >> hi == 0,
        b >> hi == 0,
    ensures
        i < hi,
        !is_bit_set!(a, i),
        is_bit_set!(b, i),
    decreases hi
{
    assert(hi != 0) by (bit_vector)
        requires a & b != b, hi <= 64, a >> hi == 0, b >> hi == 0;
    assert(1u64 << 0 == 1) by (bit_vector);
    if a & 1 != 1 && b & 1 == 1 {
        return 0;
    } else {
        assert((a >> 1) & (b >> 1) != (b >> 1) && (a >> 1) >> sub(hi, 1) == 0 && (b >> 1) >> sub(hi, 1) == 0) by (bit_vector)
            requires !(a & 1 != 1 && b & 1 == 1), a & b != b, a >> hi == 0, b >> hi == 0;
        let j = lemma_obtain_bit_index_3_aux(a >> 1, b >> 1, sub(hi, 1));
        assert(!is_bit_set!(a, add(j, 1)) && is_bit_set!(b, add(j, 1))) by (bit_vector)
            requires !is_bit_set!(a >> 1u64, j), is_bit_set!(b >> 1u64, j), j < 64;
        add(j, 1)
    }
}

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

}
