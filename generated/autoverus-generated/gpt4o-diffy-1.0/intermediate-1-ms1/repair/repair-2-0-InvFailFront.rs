
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
            old(sum).len() == 1, // Ensure sum's length is properly established here
            sum.len() == 1, // Add the invariant `sum.len() == 1` to the first loop
    {
        a.set(i, i % 1);
        i = i + 1;
    }
    i = 0;
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
            // Adding the invariant that the array `a` is not modified in this loop
            forall |k: int| 0 <= k < a.len() ==> a[k] == old(a)[k],
            // Invariants for sum[0] and a[i]
            sum[0] <= i,
            sum[0] + a[( i ) as int] <= 1 * i, // added bounds
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


//             sum.len() == 1,
//   None: sum.len() == 1

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True