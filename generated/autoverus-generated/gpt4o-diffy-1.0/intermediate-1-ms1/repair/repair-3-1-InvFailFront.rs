
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
            a.len() == old(a).len(),
            i <= N,
            old(a).len() == N,
            N > 0,
            old(sum).len() == 1,
            sum.len() == 1,
    {
        a.set(i, i % 1);
        i = i + 1;
    }
    i = 0;
    proof {
        assert(sum[0] == 0); // Added by AI
    }
    while (i < N as usize)
        invariant
            a.len() == N,
            i <= N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == (if i == 0 {
                0
            } else {
                sum[0]
            }),
            N > 0,
            forall |k: int| 0 <= k < a.len() ==> a[k] == old(a)[k],
            sum[0] <= i,
            sum[0] + a[(i) as int] <= 1 * i,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}

} // verus!


//             sum[0] == (if i == 0 {
//                 0
//             } else {
//                 sum[0]
//             }),
//   None: sum[0] == (if i == 0 {                 0             } else {                 sum[0]             })

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True