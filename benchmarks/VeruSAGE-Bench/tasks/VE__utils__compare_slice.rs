use vstd::prelude::*;
use vstd::slice::slice_index_get;

fn main() {}

verus!{

// File: src/utils.rs
/// Helper function to compare two slices.
pub fn compare_slice<'a, 'b>(x: &'a [u8], y: &'a [u8]) -> (res: bool)
    ensures
        res == (x@ =~= y@),
{
    if x.len() != y.len() {
        return false;
    }
    for i in 0..x.len()
    {
        if slice_index_get(x, i) != slice_index_get(y, i) {
            return false;
        }
    }
    true
}


}
