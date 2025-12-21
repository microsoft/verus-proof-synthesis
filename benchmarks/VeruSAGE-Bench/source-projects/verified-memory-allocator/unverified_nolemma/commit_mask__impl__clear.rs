#![verifier::exec_allows_no_decreases_clause]
use vstd::prelude::*;


fn main() {}


verus! {

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

    pub fn clear(&mut self, other: &CommitMask)
        ensures self@ == old(self)@.difference(other@)
    {
        let mut i = 0;
        while i < 8
        {
            let m = self.mask[i];
            self.mask.set(i, m & !other.mask[i]);
            i += 1;
        }
    }
}

}
