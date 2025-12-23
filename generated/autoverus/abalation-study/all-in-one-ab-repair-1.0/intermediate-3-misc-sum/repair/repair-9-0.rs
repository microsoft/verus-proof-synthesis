
assert(arith_sum_int(i as nat + 1) == arith_sum_int(i as nat) + (i as nat + 1));

After incrementing `i` and updating `sum`, this computation needs to correctly align with the values.

Let's fix the proof logic and make sure the invariant holds true. The invariant should signify that the value `sum` always matches the arithmetic sum of the first `i` numbers.

Here is the corrected code:

rust
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

    #[verifier::loop_isolation(false)]
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
                i <= n,
                sum == arith_sum_int(i as nat),
                arith_sum_int(n as nat) < 10000,
        {
            i = i + 1; // Shifted this line up
            sum = sum + i; // Use the updated value of i in the computation
        }

        proof {
            assert(arith_sum_int(i as nat) == arith_sum_int(n as nat));
        }

        sum
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpn78dta0w`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 10
// Safe: False