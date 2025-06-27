
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
    let mut idx = idx;
    while idx < n
        invariant
            idx <= n,
            *sum == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
    {
        idx = idx + 1;
        *sum = *sum + idx;
    }
}
}

// is safe: False
// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2