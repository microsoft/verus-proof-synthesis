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
    arr[i]
}

fn another_function(mut arr: Vec<u64>)
    requires
        arr.len() > 0,
        forall |i: int| 0 <= i < arr.len() ==> f(arr@, i),
    ensures
        arr@.len() == old(arr@).len(),
        forall |i: int| 0 <= i < arr.len() ==> arr@[i] == (i as u64) + 2
{
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            i <= arr.len(),
            forall |j: int| 0 <= j < arr.len() ==> f(arr@, j),
            forall |j: int| 0 <= j < i ==> arr[j] == (j as u64) + 2,
    {
        arr[i] = get_element_check_property(arr.clone(), i);
        i += 1;
    }
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1