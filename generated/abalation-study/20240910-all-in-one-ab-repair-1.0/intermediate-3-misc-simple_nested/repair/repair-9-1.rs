
use vstd::prelude::*;
fn main() {}

verus! {

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k < b.len() ==> k <= #[trigger] b[k as usize] <= k + 1,
        old(a).len() == N,
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
            forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
            i <= N as usize,
            old(a).len() == N,
            sum <= 2 * (i as i32),
            a.len() == N, 
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while j < i
            invariant
                N <= 0x3FFF_FFFF,
                a[i as int] == b[i as int] + 1,
                b.len() == N,
                forall|k: int| 0 <= k < i ==> a[k as int] == b[k as int] + 1 - k,
                j <= i,
                old(a).len() == N,
                a.len() == N, 
        {
            proof {
                assert(i < N as usize); // Confirming a[i] accesses are within bounds
            }
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        proof {
            assert(i < N as usize); // Confirming a[i] accesses are within bounds
            assert(sum <= 2 * (i as i32)); // Check the sum invariant holds
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmptpp94ubl`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False