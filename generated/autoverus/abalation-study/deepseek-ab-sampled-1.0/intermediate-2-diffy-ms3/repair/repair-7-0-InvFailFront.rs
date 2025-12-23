

use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 <= N,
            N < 1000,
            a.len() == N,
            sum.len() == 1,
            // 'a' is modified via a.set(i, ...) in this loop
            forall|k: int| 0 <= k < i ==> a[k] == (k % 3) as i32,
            forall|k: usize| k < i ==> a[(k) as int] == (k % 3) as i32,
            i <= N,
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }
    i = 0;
    proof {
        assert(old(sum)[0] == sum[0]); // Added by AI, for assertion fail
    }
    while (i < N as usize)
        invariant
            0 <= N,
            N < 1000,
            a.len() == N,
            sum.len() == 1,
            a[(i) as int] <= 2,
            // 'a' is not modified via a.set() in this loop
            // since 'k' ranges over the entire array, a[k] == (k % 3)
            // for all k satisfies a[k] <= 2
            forall|k: usize| 0 <= k < a.len() ==> a[(k) as int] == (k % 3) as i32,
            forall|k: usize| k < i ==> sum[0] == old(sum)[0] + a[(k) as int],
            i <= N,
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            i > 0 ==> sum[0] <= 2 * (i as i32),
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
        proof {
            assert(forall|k: usize| k < i ==> sum[0] == old(sum)[0] + a[(k) as int]);
        }
    }
}
}

//             sum[0] <= 2 * (i as i32),
//   None: sum[0] <= 2 * (i as i32)

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: True