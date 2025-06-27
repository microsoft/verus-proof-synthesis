
use vstd::prelude::*;
fn main() {}

verus! {

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==> k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N, // Ensure the length of 'a' matches 'N'
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
            forall|k: int| 0 <= k < i as int ==> a[k] == b[k] + 1 - k as i32,
            i <= N as usize,
            old(a).len() == N,
            sum >= i as i32,
            sum <= 2 * i as i32,
            a.len() == N,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while j < i
            invariant
                N <= 0x3FFF_FFFF,
                b.len() == N,
                a[i as int] == b[i as int] + 1,
                forall|k: int| 0 <= k < i as int ==> a[k] == b[k] + 1 - k as i32,
                j <= i,
                old(a).len() == N,
                a.len() == N,
        {
            a.set(i, a[i] - 1);
            j += 1;
        }
        sum += a[i];
        i += 1;
    }
    sum
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpa9vewopj`)
// 

// Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 10
// Safe: False