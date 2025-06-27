
use vstd::prelude::*;
fn main() {}

verus!{
     
spec fn triangle(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
    requires
        idx <= n,
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        *sum == triangle(n as nat),
{
    let mut sum_mut = *sum;
    let mut idx_mut = idx;

    while idx_mut < n
        invariant
            idx_mut <= n,
            *sum == old(*sum) + triangle(idx as nat),
            sum_mut as nat == triangle(idx_mut as nat),
    {
        idx_mut = idx_mut + 1;
        sum_mut = sum_mut + idx_mut;
    }

    *sum = sum_mut;
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1