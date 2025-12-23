
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==> b[k as usize] <= k + 1, // Small fix here to ensure index range is valid
        old(a).len() == N as usize,
        b.len() == N as usize,
        0 <= N <= 0x3FFF_FFFF, // Ensure N is non-negative
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize, // Corrected invariant to ensure 0 <= i <= N
            N <= 0x3FFF_FFFF,
            b.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k as usize] == b[k as usize] + 1,
            sum <= 2 * (i as i32),
            a.len() == N as usize, 
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= j <= i,
                N <= 0x3FFF_FFFF,
                b.len() == N as usize,
                a[i] == b[i] + 1 - j as i32,
                forall|k: int| 0 <= k < i ==> a[k as usize] == b[k as usize] + 1,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpfa_ibgt0`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False