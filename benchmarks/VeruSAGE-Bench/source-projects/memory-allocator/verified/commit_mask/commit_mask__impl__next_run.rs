#![verifier::exec_allows_no_decreases_clause]
use vstd::prelude::*;

fn main() {}

verus! {
    global size_of usize==8;

//File: config.rs
//
pub const INTPTR_SHIFT: u64 = 3;

pub const INTPTR_SIZE: u64 = 8;

pub const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

pub const SLICE_SIZE: u64 = 65536; //(1 << SLICE_SHIFT);

pub const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;

pub const SEGMENT_SIZE: u64 = (1 << SEGMENT_SHIFT);

pub const SLICES_PER_SEGMENT: u64 = (SEGMENT_SIZE / SLICE_SIZE);

pub const COMMIT_MASK_BITS: u64 = SLICES_PER_SEGMENT;
pub const COMMIT_MASK_FIELD_COUNT: u64 = COMMIT_MASK_BITS / (usize::BITS as u64);

#[verifier::external_body]
pub proof fn const_facts()
    ensures SLICE_SIZE == 65536,
        SEGMENT_SIZE == 33554432,
        SLICES_PER_SEGMENT == 512,
        COMMIT_MASK_FIELD_COUNT == 8,
{
    unimplemented!()
}

spec fn mod64(x: usize) -> usize { x % 64 }

spec fn div64(x: usize) -> usize { x / 64 }

spec fn is_bit_set(a: usize, b: usize) -> bool {
    a & (1usize << b) == (1usize << b)
}

#[allow(unused_macros)]
macro_rules! is_bit_set {
    ($a:expr, $b:expr) => {
        $a & (1u64 << $b) == (1u64 << $b)
    }
}
pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

impl CommitMask {

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

    pub fn next_run(&self, idx: usize) -> (res: (usize, usize))
        requires 0 <= idx < COMMIT_MASK_BITS,
        ensures ({ let (next_idx, count) = res;
            next_idx + count <= COMMIT_MASK_BITS
            && (forall |t| next_idx <= t < next_idx + count ==> self@.contains(t))
        }),
        // This should be true, but isn't strictly needed to prove safety:
        //forall |t| idx <= t < next_idx ==> !self@.contains(t),
        // Likewise we could have a condition that `count` is not smaller than necessary
    {
        //assert(COMMIT_MASK_BITS == 512) by (compute_only);
        //assert(COMMIT_MASK_FIELD_COUNT == 8);
        // Starting at idx, scan to find the first bit.

        proof { const_facts(); }

        let mut i: usize = idx / usize::BITS as usize;
        let mut ofs: usize = idx % usize::BITS as usize;
        let mut mask: usize = 0;

        assert(ofs < 64) by (nonlinear_arith)
            requires ofs == idx % usize::BITS as usize;
        // Changed loop condition to use 8 rather than COMMIT_MASK_FIELD_COUNT due to
        // https://github.com/verus-lang/verus/issues/925
        while i < 8
            invariant
                ofs < 64,
            ensures
                i < 8 ==> mask == self.mask[i as int] >> ofs,
                i < 8 ==> ofs < 64,
                i < 8 ==> mask & 1 == 1
        {
            mask = self.mask[i] >> ofs;
            if mask != 0 {
                while mask & 1 == 0
                    invariant
                        i < 8,
                        ofs < 64,
                        mask == self.mask[i as int] >> ofs,
                        mask != 0,
                {
                    assert((mask >> 1usize) != 0usize) by (bit_vector)
                        requires mask != 0usize, mask & 1 == 0usize;
                    assert(forall|m:u64,n:u64| #![auto] n < 64 ==> (m >> n) >> 1u64 == m >> add(n, 1u64)) by (bit_vector);
                    assert(forall|m: u64| #![auto] (m >> 63u64) >> 1u64 == 0u64) by (bit_vector);
                    mask = mask >> 1usize;
                    ofs += 1;
                }
                assert(mask & 1 == 1usize) by (bit_vector) requires mask & 1 != 0usize;
                break;
            }
            i += 1;
            ofs = 0;
        }

        if i >= COMMIT_MASK_FIELD_COUNT as usize {
            (COMMIT_MASK_BITS as usize, 0)
        } else {
            // Count 1 bits in this run
            let mut count: usize = 0;
            let next_idx = i * usize::BITS as usize + ofs;
            assert((i * 64 + ofs) % 64 == ofs) by (nonlinear_arith)
                requires ofs < 64;
            loop
                invariant_except_break
                    mask & 1 == 1,
                    i < 8,
                    mask == self.mask[i as int] >> mod64((next_idx + count) as usize),
                    (next_idx + count) / 64 == i,
                invariant
                    forall|j: usize| next_idx <= j < next_idx + count ==> #[trigger] is_bit_set(self.mask[div64(j) as int], mod64(j)),
                ensures
                    next_idx + count <= 512
            {
                assert(COMMIT_MASK_BITS == 512)by (compute_only);
                assert(COMMIT_MASK_FIELD_COUNT == 8); 
 
                loop
                    invariant_except_break
                        mask & 1 == 1,
                        i < 8,
                        mask == self.mask[i as int] >> mod64((next_idx + count) as usize),
                        (next_idx + count) / 64 == i,
                    invariant
                        forall|j: usize| next_idx <= j < next_idx + count ==> #[trigger] is_bit_set(self.mask[div64(j) as int], mod64(j)),
                    ensures
                        mask & 1 == 0,
                        (next_idx + count) / 64 == if mod64((next_idx + count) as usize) == 0 { i + 1 } else { i as int }
                {
                    proof {
                        assert(forall|m: u64, b: u64| b < 64 && #[trigger] ((m >> b) & 1) == 1 ==> is_bit_set!(m, b)) by (bit_vector);
                        reveal(is_bit_set);
                        assert(forall|j: u64, m: u64| j < 64 ==> #[trigger] ((m >> j) >> 1) == m >> add(j, 1)) by (bit_vector);
                        assert(forall|m: u64, j: u64| j >= 64 ==> #[trigger] ((m >> j) & 1) != 1) by (bit_vector);
                    }
                    count += 1;
                    mask = mask >> 1usize;

                    if (mask & 1) != 1 {
                        assert(mask & 1 == 0usize) by (bit_vector) requires mask & 1 != 1usize;
                        break;
                    }
                }

                if ((next_idx + count) % usize::BITS as usize) == 0 {
                    i += 1;
                    if i >= COMMIT_MASK_FIELD_COUNT as usize {
                        break;
                    }
                    mask = self.mask[i];
                    assert(forall|m: u64| m >> 0u64 == m) by (bit_vector);
                    ofs = 0;
                }

                if (mask & 1) != 1 {
                    break;
                }
            }

            assert forall |j: usize| next_idx <= j < next_idx + count implies self@.contains(j as int) by {
                self.lemma_view();
                assert(self@.contains(div64(j) * 64 + mod64(j)));
            };

            (next_idx, count)
        }
    }
}

}
