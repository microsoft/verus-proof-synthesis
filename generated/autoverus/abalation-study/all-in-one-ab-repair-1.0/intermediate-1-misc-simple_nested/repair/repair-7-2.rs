
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==> b[k as usize] <= k + 1,
        len(a) == N,
        len(b) == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            N <= 0x3FFF_FFFF,
            len(b) == N,
            len(a) == N,
            forall|k: int| 0 <= k < i ==> a[k as usize] == b[k as usize] + 1,
            i <= N as usize,
            sum <= 2 * (i as i32),
                len(a) == N,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                N <= 0x3FFF_FFFF,
                a[i] == b[i] + 1,
                len(b) == N,
                len(a) == N,
                forall |k: int| 0 <= k < i ==> a[k as usize] == b[k as usize] + 1,
                j <= i,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp09uxj9u0`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False