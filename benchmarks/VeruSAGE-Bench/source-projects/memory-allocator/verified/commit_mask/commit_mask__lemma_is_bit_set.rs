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
spec fn is_bit_set(a: usize, b: usize) -> bool {
    a & (1usize << b) == (1usize << b)
}

proof fn lemma_is_bit_set()
    ensures
        forall|j: usize| j < 64 ==> !(#[trigger] is_bit_set(0, j)),
        forall|j: usize| is_bit_set(!0usize, j),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a | b, j)  <==> is_bit_set(a, j) || is_bit_set(b, j),
        forall|a: usize, b: usize, j: usize| j < 64 ==> (#[trigger] is_bit_set(a & !b, j) <==> is_bit_set(a, j) && !is_bit_set(b, j)),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a & b, j)  <==> is_bit_set(a, j) && is_bit_set(b, j),
        // Implied by previous properties, possibly too aggressive trigger
        forall|a: usize, b: usize, j: usize| j < 64 ==> (a & b == 0) ==> !(#[trigger] is_bit_set(a, j) && #[trigger] is_bit_set(b, j)),
{
    reveal(is_bit_set);
    assert(forall|j: u64| #![auto] j < 64 ==> !is_bit_set!(0, j)) by (bit_vector);
    assert(forall|j: u64| #![auto] is_bit_set!(!0, j)) by (bit_vector);
    assert(forall|a: u64, b: u64, j: u64|
           (is_bit_set!(a | b, j) <==> is_bit_set!(a, j) || is_bit_set!(b, j))) by (bit_vector);
    assert(forall|a: u64, b: u64, j: u64| j < 64 ==>
           (is_bit_set!(a & !b, j) <==> is_bit_set!(a, j) && !is_bit_set!(b, j))) by (bit_vector);
    assert(forall|a: u64, b: u64, j: u64|
           (is_bit_set!(a & b, j) <==> is_bit_set!(a, j) && is_bit_set!(b, j))) by (bit_vector);
}

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

}
