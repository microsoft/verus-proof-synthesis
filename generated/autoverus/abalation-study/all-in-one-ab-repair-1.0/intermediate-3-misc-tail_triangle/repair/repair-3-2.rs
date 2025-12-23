
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

    fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
        requires
            idx <= n,
            *sum as nat == triangle(idx as nat), // Corrected requires
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *sum as nat == triangle(n as nat), // Corrected ensures
    {
        if idx < n {
            let next_idx = idx + 1;
            *sum = *sum + next_idx;
            
            proof {
                // Proof that the sum after increment is correct
                assert(*sum as nat == (triangle(idx as nat) + next_idx as nat));
            }

            tail_triangle(n, next_idx, sum);
        } else {
            proof {
                // Proof that the final sum is the correct triangle number for 'n'
                assert(*sum as nat == triangle(idx as nat));
            }
        }
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpnv01ia61`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False