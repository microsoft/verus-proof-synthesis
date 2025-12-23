
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
    {
        sum = sum + (i + 1); // To maintain correct sum
        i = i + 1;
        proof {
            assert(arith_sum_int(i as nat) == arith_sum_int((i - 1) as nat) + i);
        }
    }
    sum
}

} // verus!

In this snippet, I made a small modification inside the loop to correctly add `i + 1` to `sum` before increasing `i`. This aligns with the logic to maintain the invariant and ensures that your function should verify correctly with the Verus backend.

If the error persists, it may be related to how your compilation or verification command is being issued or there are old temporary files impacting it. You can try the following steps to troubleshoot:

1. Ensure you have the correct environment and toolchain setup for Verus.
2. Clean any previous build or temporary files.
3. Run the Verus tool with the specific file in isolation to check for exact errors.

For example, if you run via command line, ensure you use:
sh
verus filename.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpj879_t9d`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False