#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn arith_sum_int(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_int( (i - 1) as nat) }
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
            i <= n,
            sum == arith_sum_int(i as nat),
            arith_sum_int(n as nat) < 10000
    {
        i = i + 1;
        sum = sum + i;
    }

    proof {
        assert(sum == arith_sum_int(n as nat)) by {
            assert_arith_sum_int_sum(n as nat, sum);
        }
    }

    sum
}

proof fn assert_arith_sum_int_sum(n: nat, sum: u64)
    requires sum == arith_sum_int(n),
    ensures sum == arith_sum_int(n as nat),
{
    // This proof function helps Verus verify that `sum` equals `arith_sum_int(n)`
    // after the loop is done.
    assert(sum == arith_sum_int(n as nat));
}

} // verus!
// Score: (3, 2)
// Safe: True