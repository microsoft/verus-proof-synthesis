
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
        *old(sum) == triangle(idx as nat),
        triangle(n as nat) < 0x1_0000_0000,
        *sum <= u32::MAX - (n as u32), // ensure we don't overflow when adding numbers
    ensures
        *sum == triangle(n as nat),
{
    if idx < n {
        let new_idx = idx + 1;
        *sum = *sum + new_idx;
        proof {
            assert(*sum <= u32::MAX - new_idx); // prevent overflow
        }
        tail_triangle(n, new_idx, sum);
    }
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4i6ju5ac`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False