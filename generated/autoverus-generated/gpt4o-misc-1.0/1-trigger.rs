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
        forall |idx: int| 0 <= idx < arr@.len() ==> f(arr@, idx),
    ensures
        ret == i as u64 + 2,
        ret == arr@[i as int],
{
    assume(arr[( i ) as int] == i as u64 + 2);
    arr[i]
}
}

// Score: (1, 0)
// Safe: False