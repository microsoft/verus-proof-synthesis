use vstd::prelude::*;

fn main() {}

verus! {

global size_of usize==8;

#[verifier::opaque]
spec fn is_bit_set(a: usize, b: usize) -> bool {
    a & (1usize << b) == (1usize << b)
}

#[allow(unused_macros)]
macro_rules! is_bit_set {
    ($a:expr, $b:expr) => {
        $a & (1u64 << $b) == (1u64 << $b)
    }
}
proof fn lemma_bitmask_to_is_bit_set(n: usize, o: usize)
    requires
        n < 64,
        o <= 64 - n,
    ensures ({
        let m = sub(1usize << n, 1) << o;
        &&& forall|j: usize| j < o           ==> !is_bit_set(m, j)
        &&& forall|j: usize| o <= j < o + n  ==> is_bit_set(m, j)
        &&& forall|j: usize| o + n <= j < 64 ==> !is_bit_set(m, j)
    })
{
    let m = (sub(1usize << n, 1) << o) as usize;
    assert forall|j: usize| {
        &&& (j < o           ==> !is_bit_set(m, j))
        &&& (o <= j < o + n  ==> is_bit_set(m, j))
        &&& (o + n <= j < 64 ==> !is_bit_set(m, j))
    } by {
        let j = j as u64; let m = m as u64; let o = o as u64; let n = n as u64;
        reveal(is_bit_set);
        if j < 64 {
            assert(j < o               ==> !is_bit_set!(m, j)) by (bit_vector)
                requires j < 64, m == (sub(1u64 << n, 1) << o) as u64;
            assert(o <= j < add(o, n)  ==> is_bit_set!(m, j)) by (bit_vector)
                requires j < 64, m == (sub(1u64 << n, 1) << o) as u64;
            assert(add(o, n) <= j < 64 ==> !is_bit_set!(m, j)) by (bit_vector)
                requires n < 64, j < 64, m == (sub(1u64 << n, 1) << o) as u64;
        } else { }
    }
}

}
