
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)] // Attribute added for fine-grained loop verification control

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
            let idx = idx + 1;
            *sum = *sum + idx;
            proof {
            }
            tail_triangle(n, idx, sum);
        }
    }
}


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2