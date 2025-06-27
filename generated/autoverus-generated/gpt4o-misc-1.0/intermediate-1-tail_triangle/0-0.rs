
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
    if idx < n {
        let idx = idx + 1;
        *sum = *sum + idx;
        tail_triangle(n, idx, sum);
    }
}

fn loop_tail_triangle(n: u32, sum: &mut u32)
    requires
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        *sum == triangle(n as nat),
{
    let mut idx: u32 = 0;
    *sum = 0;

    while idx <= n
        invariant
            idx <= n,
            triangle(n as nat) < 0x1_0000_0000,
            *sum == triangle(idx as nat),
    {
        idx += 1;
        *sum += idx;
    }
}
}

// is safe: False
// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 6