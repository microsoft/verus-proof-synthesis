

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
    proof {
        let ghost sum0 = sum.len();
        let ghost sum_val = sum[0];
        assert(sum_val <= 0); // When i==0, sum[0] is 0
    }
    while (i < N as usize)
        invariant
            0 < N,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == k % 2,
            i <= N,
            sum.len() == 1,
            sum[0] <= i,
    {
        proof {
            let ghost current_sum = sum[0];
            if i == 0 {
                assert(current_sum == 0);
            } else {
                assert(current_sum <= i);
            }
        }
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}

//         assert(sum_val <= 0); // When i==0, sum[0] is 0
//   assertion failed: sum_val <= 0

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True