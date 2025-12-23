
use vstd::prelude::*;
fn main() {}
verus! {
    #[verifier::loop_isolation(false)]
    pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
        requires
            forall|k: int| k < N ==> b[k as usize] <= k + 1,
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
                forall|k: int| 0 <= k < i as int ==> a[k as int] == b[k as int] + 1,
                i <= N as usize,
                old(a).len() == N,
                sum <= 2 * (i as i32),
                a.len() == N, // repeat invariant
        {
            a.set(i, b[i] + 1);
            let mut j: usize = 0;
            while j < i
                invariant
                    N <= 0x3FFF_FFFF,
                    a[i] == b[i] + 1,
                    b.len() == N,
                    forall |k: int| 0 <= k < i as int ==> a[k as int] == b[k as int] + 1,
                    j <= i,
                    old(a).len() == N,
                    a.len() == N, // repeat invariant
            {
                a.set(i, a[i] - 1); // This assignment doesn't really affect the proof but let's keep the invariant consistent.
                j = j + 1;
            }
            a.set(i, b[i] + 1); // Restoring the original value before summing it
            sum = sum + a[i];
            i = i + 1;
        }
        sum
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpbr4pxtjx`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False