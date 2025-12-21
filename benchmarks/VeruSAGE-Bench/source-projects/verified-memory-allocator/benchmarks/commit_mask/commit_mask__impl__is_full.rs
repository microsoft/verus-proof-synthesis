#![verifier::exec_allows_no_decreases_clause]
use vstd::prelude::*;


fn main() {}

verus! {
    global size_of u64==8;

pub const INTPTR_SHIFT: u64 = 3;

pub const INTPTR_SIZE: u64 = 8;

pub const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

pub const SLICE_SIZE: u64 = 65536; //(1 << SLICE_SHIFT);

pub const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;


pub const SEGMENT_SIZE: u64 = (1 << SEGMENT_SHIFT);

pub const SLICES_PER_SEGMENT: u64 = (SEGMENT_SIZE / SLICE_SIZE);

pub const COMMIT_MASK_BITS: u64 = SLICES_PER_SEGMENT;


	#[verifier::external_body]
spec fn is_bit_set(a: usize, b: usize) -> bool
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn lemma_obtain_bit_index_2(a: usize) -> (b: usize)
    requires a != !0usize
    ensures
        b < 64,
        !is_bit_set(a, b)
	{
		unimplemented!()
	}

	#[verifier::external_body]
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
		unimplemented!()
	}

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

impl CommitMask{

    pub closed spec fn view(&self) -> Set<int> {
        Set::new(|t: (int, usize)|
                 0 <= t.0 < 8 && t.1 < 64
                 && is_bit_set(self.mask[t.0], t.1)
        ).map(|t: (int, usize)| t.0 * 64 + t.1)
    }

	#[verifier::external_body]
    proof fn lemma_view(&self)
        ensures
        // forall|i: int| self@.contains(i) ==> i < 512,
        // TODO: this isn't currently used but probably will need it (-> check later)
        (forall|i: int| self@.contains(i) ==> {
            let a = i / usize::BITS as int;
            let b = (i % usize::BITS as int) as usize;
            &&& a * 64 + b == i
            &&& is_bit_set(self.mask[a], b)
        }),
        forall|a: int, b: usize| 0 <= a < 8 && b < 64 && is_bit_set(self.mask[a], b)
            ==> #[trigger] self@.contains(a * 64 + b),
	{
		unimplemented!()
	}

    pub fn is_full(&self) -> (b: bool)
    ensures b == (self@ == Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS))
    {

        assert(COMMIT_MASK_BITS == 512) by (compute);
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] == !0usize
        {
            if self.mask[i] != (!0usize) {
                proof {
                    lemma_is_bit_set();
                    self.lemma_view();
                    let j = lemma_obtain_bit_index_2(self.mask[i as int]);
                    assert(!self@.contains(i * 64 + j));
                    assert(i * 64 + j < 512) by (nonlinear_arith) requires i < 8 && j < 64;
                }

                assert(COMMIT_MASK_BITS == 512) by (compute);

                assert((self@ != Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS)));
                return false;
            }
            i = i + 1;
        }
        proof {
            lemma_is_bit_set();
            self.lemma_view();
            assert forall |k: int| 0 <= k < COMMIT_MASK_BITS
                implies self@.contains(k)
            by {
                let t = k / 64;
                let u = (k % 64) as usize;
                assert(t * 64 + u == k);
                assert(is_bit_set(self.mask[t], u));
                assert(0 <= t < 8);
                assert(0 <= u < 64);
                assert(self@.contains(t * 64 + u));
            }
            assert(self@ =~= Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS));
        }

        return true;
    }
}

}
