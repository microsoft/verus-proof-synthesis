
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)] // Attribute for loop isolation

    spec fn triangle(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            n + triangle((n - 1) as nat)
        }
    }

    fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
        requires
            idx <= n,
            *old(sum) == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *sum == triangle(n as nat),
    {
        if idx < n {
            let new_idx = idx + 1;
            *sum = *sum + new_idx;
            proof { // Ensure the new sum is correct
                let new_sum = *old(sum) + new_idx as nat;
                assert(new_sum == triangle(idx as nat) + new_idx as nat);
                assert(new_sum == triangle(idx as nat) + (idx as nat + 1));
                assert(new_sum == triangle((idx as nat + 1) as nat));
                assert(new_sum == triangle(new_idx as nat));
            }
            tail_triangle(n, new_idx, sum);
        }
        proof { // For ensures
            assert(*sum == triangle(n as nat));
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmppuxzs30r`)
// 

// Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2
// Safe: False