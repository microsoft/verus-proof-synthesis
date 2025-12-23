
use vstd::prelude::*;
fn main() {}

verus! {
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
                0 <= i <= N as usize,
                N <= 0x3FFF_FFFF,
                b.len() == N,
                old(a).len() == N,
                a.len() == N,
                sum <= 2 * i as i32,
                forall|k: int| 0 <= k < i ==> a[k as usize] == b[k as usize] + 1,
        {
            a.set(i, b[i] + 1);
            let mut j: usize = 0;
            while j < i
                invariant
                    0 <= j <= i,
                    N <= 0x3FFF_FFFF,
                    b.len() == N,
                    old(a).len() == N,
                    a.len() == N,
                    a[i] == b[i] + 1,
                    forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp89_57wig`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5
// Safe: False