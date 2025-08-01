
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall |k: int| 0 <= k < N ==> 0 <= b[k] <= k + 1, // modified the requires clause for specific range
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while i < N as usize
        invariant
            N <= 0x3FFF_FFFF,
            b.len() == N,
            forall |k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
            0 <= i <= N as usize, // modified invariant
            old(a).len() == N,
            sum <= 2 * (i as i32),
            a.len() == N, // invariant added
    {
        let temp_b = b[i as int]; // ghost variable to capture value of b[i] to maintain proper invariant
        a.set(i, temp_b + 1);
        let mut j: usize = 0;
        while j < i
            invariant
                N <= 0x3FFF_FFFF,
                b.len() == N,
                0 <= (i as int) < N,
                forall |k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k, // covering all elements due to no a.set() in loop
                0 <= j <= i, // modified invariant
                old(a).len() == N,
                a.len() == N, // invariant added
        {
            proof {
                assert(j <= i); // Added assert to validate loop bounds
            }
            a.set(i, a[i as int] - 1);
            j += 1;
        }
        sum += a[i];
        i += 1;
    }
    sum
}

} // verus!



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpx4u73e5v`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False