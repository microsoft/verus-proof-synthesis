use vstd::prelude::*;
use vstd::slice::slice_index_get;

fn main() {}

verus!{

// File: src/utils.rs
pub fn compare_slice<'a, 'b>(x: &'a [u8], y: &'a [u8]) -> (res: bool)
    ensures
        res == (x@ =~= y@),
{
    if x.len() != y.len() {
        assert(x@.len() != y@.len());
        return false;
    }
    for i in 0..x.len()
        invariant
            0 <= i <= x.len(),
            x.len() == y.len(),
            forall|j: int| 0 <= j < i ==> x@[j] == y@[j],
    {
        if slice_index_get(x, i) != slice_index_get(y, i) {
            assert(x@[i as int] != y@[i as int]);
            return false;
        }
    }
    proof {
        assert(x@ =~= y@);
    }
    true
}


}
