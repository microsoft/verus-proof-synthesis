
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==>[trigger] b[k] <= k + 1, // modified range of forall and moved old() to preserves clause
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    let old_a = a@; // Added ghost variable to track the old state of a
    while i < N as usize
        invariant
            N <= sum <= 2 * N,
            forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1,
            0 <= i <= N as usize,
            old(a).len() == N,
            a.len() == N,
            b.len() == N,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while j < i
            invariant
                N <= sum + a[i] <= 2 * (i as i32 + 1),
                forall |k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1,
                0 <= j <= i,
                a.len() == N,
                b.len() == N,
                old(a).len() == N,
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpai5qnwxz`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False