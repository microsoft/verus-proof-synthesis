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

#[verifier::opaque]
spec fn is_bit_set(a: usize, b: usize) -> bool {
    a & (1usize << b) == (1usize << b)
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
    pub fn create_full(&mut self)
        ensures self@ == Set::new(|i: int| 0 <= i < COMMIT_MASK_BITS),
	{
		unimplemented!()
	}

    pub fn create(&mut self, idx: usize, count: usize)
        requires
            idx + count <= COMMIT_MASK_BITS,
            old(self)@ == Set::<int>::empty(),
        ensures self@ == Set::new(|i: int| idx <= i < idx + count),
    {
        if count == COMMIT_MASK_BITS as usize {
            self.create_full();
        } else if count == 0 {
        } else {
            let mut i = idx / usize::BITS as usize;
            let mut ofs: usize = idx % usize::BITS as usize;
            let mut bitcount = count;

            while bitcount > 0
            {
                let avail = usize::BITS as usize - ofs;
                let c = if bitcount > avail { avail } else { bitcount };
                let mask = if c >= usize::BITS as usize {
                    !0usize
                } else {
                    ((1usize << c) - 1) << ofs
                };
                self.mask.set(i, mask);
                bitcount -= c;
                ofs = 0;
                i += 1;
            }
        }
    }
}

}
