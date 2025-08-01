
use vstd::prelude::*;
fn main() {}

verus! {
    pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
        requires
            forall|k: int| 0 <= k < b.len() ==> k <= #[trigger] b[k] <= k + 1,
            old(a).len() == N as usize,
            b.len() == N as usize,
            0 <= N <= 0x3FFF_FFFF,
        ensures
            N <= sum <= 2 * N,
    {
        let mut i: usize = 0;
        let mut sum: i32 = 0;
        while i < N as usize
            invariant
                0 <= N <= 0x3FFF_FFFF,
                b.len() == N as usize,
                forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
                i <= N as usize,
                old(a).len() == N as usize,
                sum <= 2 * (i as i32),
                a.len() == N as usize,
        {
            a.set(i, b[i] + 1);
            let mut j: usize = 0;
            while j < i
                invariant
                    0 <= N <= 0x3FFF_FFFF,
                    a[i as int] == b[i as int] + 1,
                    b.len() == N as usize,
                    forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
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
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpg5qgq_cr`)
// 

// Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 11
// Safe: False