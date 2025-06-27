#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn arith_sum_int(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_int((i - 1) as nat) }
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
        0 <= i <= n,
        sum == arith_sum_int(i as nat),
    {
        proof {
            if i > 0 {
                reveal_arith_sum_int();
                assert(arith_sum_int(i as nat) == i + arith_sum_int((i - 1) as nat));
            }
        }

        i = i + 1;
        sum = sum + i;
    }
    sum
}

proof fn reveal_arith_sum_int() {
}

} // verus!
// Score: (3, 2)
// Safe: True