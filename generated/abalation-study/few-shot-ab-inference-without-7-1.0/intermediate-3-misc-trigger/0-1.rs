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

fn update_seq_elements(v: &mut Vec<u64>, N: u64) 
    requires
        old(v).len() == N,
        0 < N < 1000,
    ensures
        forall |j:int| 0<= j <v.len() ==> f(v@, j),
{
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            i <= N,
            0 < N < 1000,
            v.len() == N,
            forall |j:int| 0 <= j < i ==> f(v@, j),
    {
        v.set(i, i as u64 + 2);
        i = i + 1;
    }
}
}
// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2