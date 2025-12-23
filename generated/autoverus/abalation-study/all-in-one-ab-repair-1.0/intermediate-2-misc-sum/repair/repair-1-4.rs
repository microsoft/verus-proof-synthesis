
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
        arith_sum_int(n as nat) == sum,
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;
    while i < n
        invariant
            arith_sum_int(n as nat) < 10000,
            i <= n,
            sum == arith_sum_int(i as nat),
            arith_sum_int(n as nat) < 10000, // Repeated, clean-up not impacting verification.
    {
        i = i + 1;
        sum = sum + i;
    }
    sum
}

} // verus!

### Steps to Verify

1. **Ensure Verus Tool is Properly Installed:**
    Ensure that you have Verus installed correctly and that you are using the correct version of both Rust and Verus.

2. **Single Source File:**
    Ensure that your command-line invocation is correct and that you're providing a single filename to the verification command.

    sh
    verus compute_arith_sum.rs
    

// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpu8tmkwpu`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False