
use vstd::prelude::*;
fn main() {}

verus!{
     
spec fn triangle(n: nat) -> nat
    decreases n
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
    proof {
        // General proof to show that triangle is monotonic
        // triangle(i) ≤ triangle(j) for i ≤ j
        assert forall |i: nat, j: nat| i <= j implies triangle(i) <= triangle(j) by {
            if i <= j {
                if i < j {
                    triangle_is_monotonic(i, (j - 1) as nat);
                }
            }
        };
    } // Added by AI

    if idx < n {
        let idx = idx + 1;

        proof {
            // Assertion before the key operation
            assert(*sum + idx < 0x1_0000_0000) by {
                triangle_is_monotonic(idx as nat, n as nat);
            };
        } // Added by AI

        *sum = *sum + idx;
        tail_triangle(n, idx, sum);
    }
}

// Supporting Proof Function
proof fn triangle_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        triangle(i) <= triangle(j),
    decreases j
{
    if i < j {
        triangle_is_monotonic(i, (j - 1) as nat);
    }
}
}

// Score: (3, 0)
// Safe: True