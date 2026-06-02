#![verifier::exec_allows_no_decreases_clause]
use vstd::prelude::*;


fn main(){}

verus! {

global size_of usize == 8;


#[verifier::opaque]
spec fn is_bit_set(a: usize, b: usize) -> bool {
    a & (1usize << b) == (1usize << b)
}

pub struct CommitMask {
    mask: [usize; 8],
}

impl CommitMask{
    pub closed spec fn view(&self) -> Set<int> {
        Set::new(|t: (int, usize)|
                 0 <= t.0 < 8 && t.1 < 64
                 && is_bit_set(self.mask[t.0], t.1)
        ).map(|t: (int, usize)| t.0 * 64 + t.1)
    }

    pub fn create_empty(&mut self)
        ensures self@ == Set::<int>::empty(),
    {
        let mut i = 0;
        while i < 8
        {
            self.mask.set(i, 0);
            i += 1;
        }
    }
}

}
