
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
    let n_nat = n as nat;
    let idx_nat = idx as nat;

    if idx < n {
        let mut idx = idx + 1;
        *sum = *sum + idx;
        
        tail_triangle(n, idx, sum);
    } else {
        assert(*sum == triangle(idx_nat));
    }
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2