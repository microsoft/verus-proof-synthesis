
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
        // Corrected bug: Added explicit conversion to nat
        i + arith_sum_int((i - 1) as nat)
    }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        arith_sum_int(n as nat) == sum,
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;
    while i < n
        invariant
            arith_sum_int(n as nat) < 10000,
            i <= n,
            sum == arith_sum_int(i as nat),
    {
        i = i + 1;
        proof {
            // Corrected logic: Here we want to assert the relationship between i+1 and i
            assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i as nat);
        }
        sum = sum + i;
    }
    proof {
        // Ensure the final value relates the arith_sum_int correctly to sum
        assert(arith_sum_int(i as nat) == sum);
    }
    sum
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpibvn2n0l`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: True