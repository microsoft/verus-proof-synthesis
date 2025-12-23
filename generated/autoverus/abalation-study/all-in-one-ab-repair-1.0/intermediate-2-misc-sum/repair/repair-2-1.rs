
proof {
    assert(arith_sum_int(i as nat) == sum);
}
is inside the loop but this needs to be checked after updating the invariant by incrementing `sum`. This assertion is incorrect inside the loop body because `sum` is set to `sum + i` before the loop restarts.

Here is the fixed version of your code:

rust
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}
verus! {

spec fn arith_sum_int(i: nat) -> nat
    decreases i,
{
    if i == 0 {
        0
    } else {
        i + arith_sum_int((i - 1) as nat)
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
            i <= n,
            sum == arith_sum_int(i as nat),
            arith_sum_int(n as nat) < 10000,
    {
        i = i + 1;
        sum = sum + i;
    }
    proof {
        assert(arith_sum_int(n as nat) == sum);
    }
    sum
}

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpmftpz1xx`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7
// Safe: False