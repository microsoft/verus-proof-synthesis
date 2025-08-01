
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
        requires
            forall|k: int| k >= 0 && k < N ==> #[trigger] 0 <= b[k] <= k + 1,
            old(a).len() == N,
            b.len() == N,
            N >= 0,
            N <= 0x3FFF_FFFF,
        ensures
            N <= sum <= 2 * N,
    {
        let mut i: usize = 0;
        let mut sum: i32 = 0;
        while i < N as usize
            invariant
                N >= 0,
                N <= 0x3FFF_FFFF,
                b.len() == N,
                old(a).len() == N,
                a.len() == N,
                i <= N as usize,
                sum <= 2 * (i as i32),
                forall|k: int| 0 <= k < i as int ==> a[k] == b[k] + 1,
        {
            a.set(i, b[i] + 1);
            let mut j: usize = 0;
            while j < i
                invariant
                    N >= 0,
                    N <= 0x3FFF_FFFF,
                    b.len() == N,
                    old(a).len() == N,
                    a.len() == N,
                    j <= i,
                    forall|k: int| 0 <= k < j as int ==> a[k] == b[k] + 1,
                    a[i] == b[i] + 1 - j as i32,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp2suy3zzl`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False