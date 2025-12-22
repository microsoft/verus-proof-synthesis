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

proof fn lemma_obtain_bit_index_2(a: usize) -> (b: usize)
    requires a != !0usize
    ensures
        b < 64,
        !is_bit_set(a, b)
{
    reveal(is_bit_set);
    assert(!a != 0usize) by (bit_vector)
        requires a != !0usize;
    let b = lemma_obtain_bit_index_1(!a) as u64;
    let a = a as u64;
    assert(!is_bit_set!(a, b)) by (bit_vector)
        requires b < 64 && !a & (1u64 << b) == (1usize << b);
    b as usize
}

	#[verifier::external_body]
proof fn lemma_obtain_bit_index_1(a: usize) -> (b: usize)
    requires a != 0
    ensures
        b < 64,
        is_bit_set(a, b)
	{
		unimplemented!()
	}

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

}
