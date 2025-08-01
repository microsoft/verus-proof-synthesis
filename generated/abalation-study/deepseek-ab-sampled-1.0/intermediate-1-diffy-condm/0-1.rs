

use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun(a: &mut Vec<i32>, N: u32)
    requires
        N > 0,
        old(a).len() == N,
    ensures
        forall |k: int| 0 <= k < N ==> a[k] % 2 == N % 2,
{
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            // Invariant 1: Bound on i to ensure it doesn't exceed N
            i <= N as usize,
            // Invariant 2: Maintain N > 0
            N > 0,
            // Invariant 3: Track the state of the array a up to index i
            forall |k: int| 0 <= k < (i as int) ==> a[k] == 0,
    {
        a.set(i, 0);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            // Invariant 1: Bound on i to ensure it doesn't exceed N
            i <= N as usize,
            // Invariant 2: Maintain N > 0
            N > 0,
            // Invariant 3: Each element not yet processed maintains initial value after first loop
            forall |k: int| (i as int) <= k < N as int ==> a[k] == 0,
            // Invariant 4: Elements processed so far satisfy the required condition
            forall |k: int| 0 <= k < (i as int) ==> a[k] % 2 == (N % 2),
    {
        if (N % 2 == 0) {
            a.set(i, a[i] + 2);
        } else {
            a.set(i, a[i] + 1);
        }
        i = i + 1;
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 7