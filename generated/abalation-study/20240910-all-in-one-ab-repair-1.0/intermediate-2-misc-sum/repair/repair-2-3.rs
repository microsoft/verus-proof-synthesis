
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
        // invariant before entering the loop
        proof {
            assert(i <= n);
            assert(sum == arith_sum_int(i as nat));
        }
        while i < n
            invariant
                i <= n,
                sum == arith_sum_int(i as nat),
                arith_sum_int(n as nat) < 10000,
        {
            i = i + 1;
            sum = sum + i;
            // assert invariant within the loop
            proof {
                assert_sum_correctness(i, sum); // using a helper function to assert correctness
            }
        }
        sum
    }

    // Helper function to assert the correctness within the loop
    proof fn assert_sum_correctness(new_i: u64, new_sum: u64)
        requires
            new_i > 0,
        ensures
            arith_sum_int(new_i as nat) == new_sum
    {
        let prev_i = new_i - 1;
        assert(arith_sum_int(new_i as nat) == new_sum);
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpqs8m9us9`)
// 

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True