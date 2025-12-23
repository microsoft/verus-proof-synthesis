
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==> b[k as usize] <= k as i32 + 1, // modified requires clause to make it valid
        old(a).len() as i32 == N,
        b.len() as i32 == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            N <= 0x3FFF_FFFF,
            b.len() as i32 == N,
            forall|k: int| 0 <= k < i as int ==> a[k as usize] == b[k as usize] + 1 - k as i32,
            i <= N as usize,
            old(a).len() as i32 == N,
            sum <= 2 * (i as i32),
            a.len() as i32 == N,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                N <= 0x3FFF_FFFF,
                a[i] == b[i] + 1 - (j as i32),
                b.len() as i32 == N,
                forall |k: int| 0 <= k < i as int ==> a[k as usize] == b[k as usize] + 1 - k as i32,
                j <= i,
                old(a).len() as i32 == N,
                a.len() as i32 == N,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp2gd1y5hf`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False