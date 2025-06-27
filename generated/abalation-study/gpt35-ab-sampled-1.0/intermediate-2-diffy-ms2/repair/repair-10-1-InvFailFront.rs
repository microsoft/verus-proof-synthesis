
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
        let mut i: usize = 0;

        assert!(sum.len() == 1); // Assert the invariant before the loop

        while (i < N as usize)
            invariant
                a.len() == N,
                i <= N,
        {
            a.set(i, i % 2);
            i = i + 1;
        }

        // Rest of the code remains the same
    }
}


//                 sum.len() == 1,
//   None: sum.len() == 1

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False