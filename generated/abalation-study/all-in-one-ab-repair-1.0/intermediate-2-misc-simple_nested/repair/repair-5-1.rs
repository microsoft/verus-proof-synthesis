
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
        requires
            forall |k: int| 0 <= k < b.len() ==> b[k] <= k + 1, // Updated the range check for b
            old(a).len() == b.len(),
            b.len() as i32 == N, // Modified the len equivalence to int N
            0 <= N <= 0x3FFF_FFFF, // Ensure N is non-negative and within bounds
        ensures
            N <= sum <= 2 * N,
    {
        let mut i: usize = 0;
        let mut sum: i32 = 0;
        while i < N as usize
            invariant
                0 <= N <= 0x3FFF_FFFF,
                b.len() as i32 == N,
                forall |k: int| 0 <= k < i as int ==> a[k as int] == b[k as int] + 1 - k,
                i <= N as usize,
                old(a).len() == b.len(),
                sum <= 2 * (i as i32),
                a.len() == b.len(), // Ensuring a's length remains unchanged
        {
            a.set(i, b[i] + 1);
            let mut j: usize = 0;
            while j < i
                invariant
                    0 <= N <= 0x3FFF_FFFF,
                    b.len() as i32 == N,
                    a[i as int] == b[i as int] + 1,
                    forall |k: int| 0 <= k < i as int ==> a[k as int] == b[k as int] + 1 - k,
                    j <= i,
                    old(a).len() == b.len(),
                    a.len() == b.len(), // Ensuring a's length remains unchanged
            {
                a.set(i, a[i] - 1);
                j = j + 1;
            }
            sum = sum + a[i];
            i = i + 1;
        }
        return sum;
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpj8947ees`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: False