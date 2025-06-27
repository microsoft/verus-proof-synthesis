
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
        requires
            N > 0,
            forall|k: int| 0 <= k < N ==> -0x3FFF_FFFF <= b[k as usize] <= 0x3FFF_FFFF,
            old(a).len() == N as usize,
            b.len() == N as usize,
            N <= 0x3FFF_FFFF,
        ensures
            result >= 0 && result <= 2 * N,
    {
        let mut i: usize = 0;
        let mut sum: i32 = 0;
        while i < N as usize
            invariant
                N <= 0x3FFF_FFFF,
                b.len() == N as usize,
                forall|k: int| 0 <= k < i as int ==> a[k as usize] == b[k as usize] + 1,
                i <= N as usize,
                old(a).len() == N as usize,
                sum >= 0 && sum <= 2 * (i as i32),
                a.len() == N as usize,
        {
            a.set(i, b[i] + 1);
            let mut j: usize = 0;
            while j < i
                invariant
                    N <= 0x3FFF_FFFF,
                    a[i] == b[i] + 1,
                    b.len() == N as usize,
                    forall|k: int| 0 <= k < i as int ==> a[k as usize] == b[k as usize] + 1,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpkfxt5jev`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False