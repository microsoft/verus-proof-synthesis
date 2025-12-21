#![verifier::exec_allows_no_decreases_clause]
use vstd::prelude::*;

fn main(){}


verus! {

    global size_of usize==8;

pub const INTPTR_SHIFT: u64 = 3;

pub const INTPTR_SIZE: u64 = 8;

pub const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

pub const SLICE_SIZE: u64 = 65536; //(1 << SLICE_SHIFT);

pub const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;


pub const SEGMENT_SIZE: u64 = (1 << SEGMENT_SHIFT);

pub const SLICES_PER_SEGMENT: u64 = (SEGMENT_SIZE / SLICE_SIZE);

pub const COMMIT_MASK_BITS: u64 = SLICES_PER_SEGMENT;

spec fn mod64(x: usize) -> usize { x % 64 }

	#[verifier::external_body]
spec fn is_bit_set(a: usize, b: usize) -> bool
	{
		unimplemented!()
	}

	#[verifier::external_body]
proof fn lemma_bitmask_to_is_bit_set(n: usize, o: usize)
    requires
        n < 64,
        o <= 64 - n,
    ensures ({
        let m = sub(1usize << n, 1) << o;
        &&& forall|j: usize| j < o           ==> !is_bit_set(m, j)
        &&& forall|j: usize| o <= j < o + n  ==> is_bit_set(m, j)
        &&& forall|j: usize| o + n <= j < 64 ==> !is_bit_set(m, j)
}),
	{
		unimplemented!()
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

	#[verifier::external_body]
    proof fn lemma_change_one_entry(&self, other: &Self, i: int)
        requires
            0 <= i < 8,
            self.mask[i] == 0,
            forall|j: int| 0 <= j < i ==> other.mask[j] == self.mask[j],
            forall|j: int| i < j < 8 ==> other.mask[j] == self.mask[j],
        ensures
            other@ == self@.union(Set::new(|b: usize| b < 64 && is_bit_set(other.mask[i], b)).map(|b: usize| 64 * i + b)),
	{
		unimplemented!()
	}

    pub fn create(&mut self, idx: usize, count: usize)
        requires
            idx + count <= COMMIT_MASK_BITS,
            old(self)@ == Set::<int>::empty(),
        ensures self@ == Set::new(|i: int| idx <= i < idx + count),
    {
        proof {
            //const_facts();
            lemma_is_bit_set();
            self.lemma_view();
            assert forall|i: int| 0 <= i < 8 implies self.mask[i] == 0 by {
                if self.mask[i] != 0 {
                    let j = lemma_obtain_bit_index_1(self.mask[i]);
                    assert(self@.contains(i * 64 + j));
                }
            }
        }
        if count == COMMIT_MASK_BITS as usize {
            self.create_full();
        } else if count == 0 {
            assert(self@ =~= Set::new(|i: int| idx <= i < idx + count));
        } else {
            let mut i = idx / usize::BITS as usize;
            let mut ofs: usize = idx % usize::BITS as usize;
            let mut bitcount = count;

            assert(COMMIT_MASK_BITS == 512) by (compute_only);

            assert(Set::new(|j: int| idx <= j < idx + (count - bitcount)) =~= Set::empty());
            while bitcount > 0
                invariant
                    self@ == Set::new(|j: int| idx <= j < idx + (count - bitcount)),
                    ofs == if count == bitcount { idx % 64 } else { 0 },
                    bitcount > 0 ==> 64 * i + ofs == idx + (count - bitcount),
                    idx + count <= 512,
                    forall|j: int| i <= j < 8 ==> self.mask[j] == 0,
                    bitcount <= count,
            {
                assert(i < 8) by (nonlinear_arith)
                    requires
                        idx + (count - bitcount) < 512,
                        i == (idx + (count - bitcount)) / 64;
                let avail = usize::BITS as usize - ofs;
                let c = if bitcount > avail { avail } else { bitcount };
                let mask = if c >= usize::BITS as usize {
                    !0usize
                } else {
                    assert((1usize << c) > 0usize) by (bit_vector) requires c < 64usize;
                    ((1usize << c) - 1) << ofs
                };
                let old_self = Ghost(*self);
                self.mask.set(i, mask);
                let oi = Ghost(i);
                let obc = Ghost(bitcount);
                let oofs = Ghost(ofs);
                bitcount -= c;
                ofs = 0;
                i += 1;
                proof {
                    assert(forall|a: u64| a << 0u64 == a) by (bit_vector);
                    let oi   = oi@;
                    let obc  = obc@;
                    let oofs = oofs@;
                    lemma_is_bit_set();
                    old_self@.lemma_change_one_entry(self, oi as int);
                    assert(self@ == old_self@@.union(Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b)));
                    // TODO: a lot of duplicated proof structure here, should be able to
                    // somehow lift that structure out of the if-else
                    if oofs > 0 { // first iteration
                        assert(Set::new(|j: int| idx <= j < idx + (count - bitcount))
                               =~= Set::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount)));
                        if obc < 64 {
                            assert(mask == sub(1usize << c, 1usize) << oofs);
                            lemma_bitmask_to_is_bit_set(c, oofs);
                            assert(Set::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount))
                                   =~= Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                            by {
                                let s1 = Set::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount));
                                let s2 = Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                                assert(forall|j: usize| idx + (count - obc) <= j < idx + (count - bitcount) ==> #[trigger] is_bit_set(self.mask[oi as int], mod64(j)));
                                assert forall|x: int| s1.contains(x) implies s2.contains(x) by {
                                    let b = x % 64;
                                    assert(Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                                }
                            }
                            assert(Set::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount))
                                   =~= Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                        } else {
                            assert(mask == sub(1usize << sub(64usize, oofs), 1usize) << oofs);
                            lemma_bitmask_to_is_bit_set(sub(64, oofs), oofs);
                            assert(Set::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount))
                                   =~= Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                            by {
                                let s1 = Set::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount));
                                let s2 = Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                                assert forall|x: int| s1.contains(x) implies s2.contains(x) by { // unstable
                                    assert(Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                                }
                            }
                            assert(Set::new(|j: int| idx + (count - obc) <= j < idx + (count - bitcount))
                                   =~= Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                        }
                    } else if obc < 64 { // last iteration
                        assert(Set::new(|j: int| idx <= j < idx + (count - bitcount))
                               =~= Set::new(|j: int| idx <= j < idx + (count - obc))
                                   .union(Set::new(|j: int| idx + (count - obc) <= j < idx + count)));
                        assert(mask == (1usize << obc) - 1usize);
                        lemma_bitmask_to_is_bit_set(obc, 0);
                        assert(Set::new(|j: int| idx + (count - obc) <= j < idx + count)
                               =~= Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                        by {
                            let s1 = Set::new(|j: int| idx + (count - obc) <= j < idx + count);
                            let s2 = Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                            assert forall|x: int| s1.contains(x) implies s2.contains(x) by {
                                assert(Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                            }
                        }
                        assert(Set::new(|j: int| idx + (count - obc) <= j < idx + count)
                               =~= Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                    } else {
                        assert(Set::new(|j: int| idx <= j < idx + (count - bitcount))
                               =~= Set::new(|j: int| idx <= j < idx + (count - obc))
                                   .union(Set::new(|j: int| idx + (count - obc) <= j < idx + (count - obc) + 64)));
                        assert(mask == !0usize);
                        let new = Set::new(|j: int| idx + (count - obc) <= j < idx + (count - obc) + 64);
                        assert(Set::new(|j: int| 64 * oi <= j < 64 * oi + 64)
                               =~= Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b))
                        by {
                            let s1 = Set::new(|j: int| 64 * oi <= j < 64 * oi + 64);
                            let s2 = Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b);
                            assert forall|x: int| s1.contains(x) implies s2.contains(x) by {
                                assert(Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).contains((x % 64) as usize));
                            }
                        }
                        assert(Set::new(|j: int| 64 * oi <= j < 64 * oi + 64)
                               =~= Set::new(|b: usize| b < 64 && is_bit_set(self.mask[oi as int], b)).map(|b: usize| 64 * oi + b));
                    }
                }
                assert(self@ =~= Set::new(|j: int| idx <= j < idx + (count - bitcount)));
            }
        }
    }

	#[verifier::external_body]
    pub fn create_full(&mut self)
        ensures self@ == Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS),
	{
		unimplemented!()
	}
}

}
