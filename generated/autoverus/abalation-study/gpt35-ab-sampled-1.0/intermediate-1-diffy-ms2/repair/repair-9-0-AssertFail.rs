
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
                0 <= i <= N,
                a.len() == N,
                forall|k: int| 0 <= k < i ==> a[k] == k % 2,
                old(a).len() == N,
                old(sum).len() == 1,
                sum.len() == 1,
                N > 0,
        {
            a.set(i, i % 2);
            i = i + 1;
        }
        i = 0;
        proof {
            assert(sum[0] <= i);
        }
        while (i < N as usize)
            invariant
                0 <= i <= N,
                a.len() == N,
                forall|k: int| 0 <= k <= i ==> a[k] == k % 2,
                old(a).len() == N,
                old(sum).len() == 1,
                sum.len() == 1,
                sum[0] <= i,
                N > 0,
            {
                if (i == 0) {
                    sum.set(0, 0);
                } else {
                    sum.set(0, sum[0] + a[i]);
                }
                i = i + 1;
                assert(sum[0] <= i);
                proof {
                    assert(forall|k: int| 0 <= k < i ==> a[k] == k % 2);
                }
            }
        }
    }
}


//                 assert(forall|k: int| 0 <= k <= i ==> a[k] == k % 2);
//   assertion failed: forall|k: int| 0 <= k <= i ==> a[k] == k % 2

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False