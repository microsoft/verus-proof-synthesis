
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}
verus! {

spec fn arith_sum_int(i: nat) -> nat
    decreases i,
{
    if i == 0 {
        0
    } else {
        i + arith_sum_int((i - 1) as nat)
    }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        sum == arith_sum_int(n as nat),
{
    let mut i: u64 = 0; // Start from 0
    let mut sum: u64 = 0; // Start with sum as 0
    while i < n
        invariant
            arith_sum_int(n as nat) < 10000,
            i <= n,
            sum == arith_sum_int(i as nat),
    {
        sum = sum + (i + 1); // Corrected to add (i + 1)
        proof {
            assert(arith_sum_int((i + 1) as nat) == arith_sum_int((i - 1) as nat) + i as nat + 1);
        }
        i = i + 1;
    }
    sum // Return the computed sum
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpp92cvvgf`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False