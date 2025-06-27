
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]
   
    spec fn triangle(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            n + triangle((n - 1) as nat)
        }
    }

    fn tail_triangle(n: u32, mut idx: u32, sum: &mut u32)
        requires
            idx <= n,
            *sum == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *sum == triangle(n as nat),
    {
        while idx < n
            invariant
                idx <= n,
                *sum == triangle(idx as nat),
        {
            idx += 1;
            *sum += idx;
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpeliflt9r`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False