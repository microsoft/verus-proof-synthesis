
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==> b[k] <= k + 1, // Corrected range of k
        old(a).len() == N as usize, // Ensure len constraint on usize
        b.len() == N as usize, // Ensure len constraint on usize
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while i < N as usize
        invariant
            N <= 0x3FFF_FFFF,
            b.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1 - k as i32, // Corrected type cast
            i <= N as usize,
            old(a).len() == N as usize, // Ensure len constraint on usize
            sum <= 2 * (i as i32),
            a.len() == N as usize, // invariant added
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while j < i
            invariant
                N <= 0x3FFF_FFFF,
                a[i] == b[i] + 1 - j as i32, // Corrected type cast
                b.len() == N as usize,
                forall |k: int| 0 <= k < i ==> a[k] == b[k] + 1 - k as i32, // Corrected type cast
                j <= i,
                old(a).len() == N as usize, // Ensure len constraint on usize
                a.len() == N as usize, // invariant added
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

// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 11


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp5zam4zun`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False