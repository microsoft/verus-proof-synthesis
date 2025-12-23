
use vstd::prelude::*;
fn main() {}

verus! {
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k < N ==> b[k as usize] <= k as i32 + 1,
        a.len() == N as usize,
        b.len() == N as usize,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while i < N as usize
        invariant
            N <= 0x3FFF_FFFF,
            b.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k as usize] == b[k as usize] + 1 - k as i32,
            i <= N as usize,
            sum <= 2 * (i as i32),
            a.len() == N as usize,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while j < i
            invariant
                N <= 0x3FFF_FFFF,
                a[i as usize] == b[i as usize] + 1,
                b.len() == N as usize,
                forall|k: int| 0 <= k < i ==> a[k as usize] == b[k as usize] + 1 - k as i32,
                j <= i,
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
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpr5l8vxsa`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False