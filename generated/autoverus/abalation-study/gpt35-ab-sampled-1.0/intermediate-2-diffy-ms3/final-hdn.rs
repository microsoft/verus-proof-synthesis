
use vstd::prelude::*;

fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
    pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
    {
        let mut i: usize = 0;
        while (i < N as usize)
            invariant
                N < 1000,
                N > 0,
                a.len() == N as usize,
                i <= N as usize,
        {
            a.set(i, (i % 3) as i32);
            i = i + 1;
        }
        i = 0;
        
        // Add the invariant as an assert right before the loop

        while (i < N as usize)
            invariant
                N < 1000,
                N > 0,
                a.len() == N as usize,
                i <= N as usize,
                0 <= i, // Added by AI
        {
            if (i == 0) {
                sum.set(0, 0);
            } else {
                sum.set(0, sum[0] + a[i]);
            }
            i = i + 1;
        }
    }
} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5