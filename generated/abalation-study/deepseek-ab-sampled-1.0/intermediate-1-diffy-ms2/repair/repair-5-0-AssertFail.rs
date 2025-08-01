
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
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize) 
        invariant
            0 < N,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == k % 2,
            i <= N,
            sum.len() == 1,
    {
        a.set(i, i % 2);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize) 
        invariant
            0 < N,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == k % 2,
            i <= N,
            sum.len() == 1,
            sum[0] <= i,
    {
        if (i == 0) {
            sum.set(0, 0);
            proof {
                // Check sum[0] after initialization
                assert(sum[0] <= 0); 
            }
        } else {
            proof {
                // Ensure sum[0] does not decrease
                assert(sum[0] >= old(sum[0]));
            }
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}


//         assert(sum[0] <= 0); // When i==0, sum[0] is 0
//   assertion failed: sum[0] <= 0

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True