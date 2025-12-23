
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==> #[trigger] b[k as int] <= k + 1,
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
            0 <= i <= N as usize,
            N <= 0x3FFF_FFFF,
            b.len() == N as usize,
            old(a).len() == N as usize,
            forall|k: int| 0 <= k < i as int ==> a[k as int] == b[k as int] + 1 - k as i32,
            sum <= 2 * (i as i32),
    {
        a.set(i, b[i] + 1);
        
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i,
                a[i as int] == b[i as int] + 1,
                b.len() == N as usize,
                old(a).len() == N as usize,
                forall |k: int| 0 <= k < i as int ==> a[k as int] == b[k as int] + 1 - k as i32,
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


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp9unl4l66`)
// 

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: False