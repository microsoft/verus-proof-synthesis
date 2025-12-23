
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==> b[k] <= k + 1, // ensuring k is within bounds
        old(a).len() == N as usize,
        b.len() == N as usize,
        0 <= N <= 0x3FFF_FFFF, // ensures N is within a valid range
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while i < N as usize
        invariant
            0 <= i <= N as usize, // ensuring i is within bounds
            forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
            a.len() == N as usize,
            b.len() == N as usize,
            sum <= 2 * (i as i32),
            old(a).len() == N as usize, // same size as initially,
            0 <= N <= 0x3FFF_FFFF,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i, // ensuring j is within bounds
                a[i as int] == b[i as int] + 1 - j,
                forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
                a.len() == N as usize,
                b.len() == N as usize,
                old(a).len() == N as usize, // same size as initially
                0 <= N <= 0x3FFF_FFFF,
        {
            a.set(i, a[i] - 1);
            j += 1;
        }
        sum += a[i];
        i += 1;
    }
    sum
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpuc8msxyn`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: False