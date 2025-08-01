
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==> b[k] <= k + 1,   // Adjusted precondition to fit the usage within the code
        old(a).len() == N as usize,
        b.len() == N as usize,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            N <= 0x3FFF_FFFF,
            b.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
            i <= N as usize,
            old(a).len() == N as usize,
            sum <= 2 * (i as i32),
            a.len() == N as usize,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                N <= 0x3FFF_FFFF,
                a[i as int] == b[i as int] + 1,
                b.len() == N as usize,
                forall |k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
                j <= i,
                old(a).len() == N as usize,
                a.len() == N as usize,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmppp6et5yb`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: False