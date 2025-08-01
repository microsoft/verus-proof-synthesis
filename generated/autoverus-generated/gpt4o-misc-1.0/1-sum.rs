
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn arith_sum_int(i: nat) -> nat
    decreases i,
{
    if i == 0 {
        0
    } else {
        i + arith_sum_int((i - 1) as nat)
    }
}

// Lemma function to help prove the bound
proof fn lemma_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        arith_sum_int(i) <= arith_sum_int(j),
    decreases j
{
    if i < j {
        lemma_monotonic(i, (j-1) as nat);
    }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        arith_sum_int(n as nat) == sum,
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;
    while i < n
        invariant
            arith_sum_int(n as nat) < 10000,
            i <= n,
            sum == arith_sum_int(i as nat),
            arith_sum_int(n as nat) < 10000,
    {
        i = i + 1;

        // Add assertions to prevent overflow
        assert(arith_sum_int(i as nat) <= arith_sum_int(n as nat)) by {
            lemma_monotonic(i as nat, n as nat);
        };
        assert(sum + i <= arith_sum_int(n as nat)) by {
            lemma_monotonic(i as nat, n as nat);
        };

        sum = sum + i;
    }
    sum
}

} // verus!

// Score: (4, 0)
// Safe: True