
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize)
        requires
            old(a).len() == N,
            old(sum).len() == 1,
            N > 0,
        ensures
            sum[0] <= N,
    {
        // ... (unchanged code)

        // Add assert statement before the loop
        assert!(sum.len() == 1);

        while (i < N as usize)
            invariant
                forall|j: int| 1 <= j <= i ==> sum[j - 1] + a[j] >= 0,
                i <= N,
                // ... (other invariants)
        {
            // ... (unchanged loop body)
        }
    }
}


//                 sum.len() == 1,
//   None: sum.len() == 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False