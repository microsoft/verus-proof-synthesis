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

fn loop_example(arr: &mut Vec<u64>, n: usize)
    requires
        arr.len() == n,
    ensures
        forall |j: int| 0 <= j < n ==> arr[j as int] == j as u64 + 2,
{
    let mut i: usize = 0;

    while i < n
        invariant 
            i <= n,
            arr.len() == n,
            forall |j: int| 0 <= j < i as int ==> arr[j as int] == j as u64 + 2,
    {
        arr.set(i, i as u64 + 2);
        i = i + 1;
    }
}
}


// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1