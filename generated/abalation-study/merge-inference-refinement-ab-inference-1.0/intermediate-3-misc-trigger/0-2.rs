#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus!{
spec fn f(seq: Seq<u64>, i: int) -> bool {
    seq[i] == i + 2
}

fn get_element_check_property(arr: Vec<u64>, i: usize) -> (ret: u64)
    requires
        arr.len() > 0,
        0 < i < arr@.len(),
        forall |j: int| 0 <= j < arr@.len() ==> f(arr@, j),
    ensures
        ret == i + 2,
        ret == arr@[i as int],
{
    arr[i]
}
}
// is safe: False
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1