
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_invariant(self)]
    pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
        requires
            forall|k: int| 0 <= k < N ==> 0 <= #[trigger] b[k as usize] <= k + 1,
            old(a).len() == N,
            b.len() == N,
            N <= 0x3FFF_FFFF,
        ensures
            N <= sum <= 2 * N,
    {
        let mut i: usize = 0;
        let mut sum: i32 = 0;
        while (i < N as usize)
            invariant
                N <= 0x3FFF_FFFF,
                b.len() == N,
                forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
                old(a).len() == N,
                sum <= 2 * (i as i32),
                i <= N as usize,
                a.len() == N,
        {
            a.set(i, b[i] + 1);
            let mut j: usize = 0;
            while (j < i)
                invariant
                    N <= 0x3FFF_FFFF,
                    b.len() == N,
                    a.len() == N,
                    a[i as int] == b[i as int] + 1 - j as i32,
                    forall |k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
                    j <= i,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpleqred9g`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False