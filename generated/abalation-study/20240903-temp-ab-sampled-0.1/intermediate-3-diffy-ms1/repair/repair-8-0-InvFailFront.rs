
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] == 0,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == k % 1,
            i <= N,
            sum.len() == 1,
            N > 0,
    {
        a.set(i, i % 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            // The array `a` is not modified in this loop
            forall|k: int| 0 <= k < N ==> a[k] == k % 1,
            sum.len() == 1,
            N > 0,
            i > 0 ==> sum[0] == 0, // Modified invariant
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
    proof {
        assert(sum.len() == 1);
        assert(sum[0] == 0); // This assertion fails because the sum is modified in the second loop
    }
}

} // verus!


//             sum[0] == 0, // Added by AI, for assertion fail
//   None: sum[0] == 0

// Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True