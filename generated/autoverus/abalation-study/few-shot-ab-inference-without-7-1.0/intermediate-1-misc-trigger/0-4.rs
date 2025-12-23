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
        forall |i: int| f(arr@, i),
    ensures
        ret == i + 2,
        ret == arr@[i as int],
{ 
    let mut j: usize = 0;
    while j < arr.len()
        invariant
            j <= arr.len(),
            arr.len() > 0,
            0 < i < arr@.len(),
            forall |k: int| f(arr@, k),
            forall |k: int| 0 <= k < j ==> arr[k as int] == k + 2,
    {
        j = j + 1;
    }

    arr[i]
}
}

// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1