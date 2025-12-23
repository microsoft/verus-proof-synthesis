
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
            forall|k: int| 0 <= k < N ==> a[k] == k % 1, // The array `a` is not modified in this loop
            forall|k: int|
                0 <= k < i ==> sum[0] == (if k == 0 {
                    0
                } else {
                    sum[0] + a[k]
                }),
            i <= N,
            sum.len() == 1,
            N > 0,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
        proof {
            if i > 1 { // Fixed by AI
                assert(forall|k: int| 0 <= k < i ==> sum[0] == (if k == 0 { 0 } else { sum[0] + a[k] }));
            }
        } // Added by AI
    }
}

} // verus!


//             forall|k: int|
//                 0 <= k < i ==> sum[0] == (if k == 0 {
//                     0
//                 } else {
//                     sum[0] + a[k]
//                 }),
//   None: forall|k: int|                 0 <= k < i ==> sum[0] == (if k == 0 {                     0                 } else {                     sum[0] + a[k]                 })

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True