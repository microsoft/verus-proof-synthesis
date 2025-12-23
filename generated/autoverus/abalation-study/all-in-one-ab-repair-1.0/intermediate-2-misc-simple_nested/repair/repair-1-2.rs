
use vstd::prelude::*;
fn main() {}
verus! {

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k < b.len() ==> b[k] <= k + 1,
        a.len() == N,
        b.len() == N,
        0 <= N <= 0x3FFF_FFFF,
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
            forall|k: int| 0 <= k < i as int ==> a[k as int] == b[k as int] + 1 - k,
            old(a).len() == N,
            a.len() == N,
            sum <= 2 * (i as i32),
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i,
                a.len() == N,
                forall |k: int| 0 <= k < i as int ==> a[k as int] == b[k as int] + 1 - k,
                N <= 0x3FFF_FFFF,
                a[(i) as int] == b[(i) as int] + 1 - j,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpffpgs2jb`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False