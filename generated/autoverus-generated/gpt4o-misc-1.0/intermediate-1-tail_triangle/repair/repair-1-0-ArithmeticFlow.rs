
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

proof fn lemma_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        triangle(i) <= triangle(j),
    decreases j
{
    if i < j {
        lemma_monotonic(i, ( (j - 1) ) as nat);
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

        // Add assertion before modifying sum
        assert(*sum as u64 + idx as u64 <= 0xFFFF_FFFFu64);
        assert((*sum + idx) as u64 <= triangle(n as nat) as u64) by {
            lemma_monotonic(idx as nat, n as nat);
        };

        *sum = *sum + idx;
        tail_triangle(n, idx, sum);
    }
}

} // verus!



//         *sum = *sum + idx;
//   None: *sum + idx

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1
// Safe: True