
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        a.len() == N,
        sum.len() == 1,
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
            a[(i) as int] <= 2,
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
        assert(0 <= N);
        assert(N < 1000);
        assert(sum[0] == old(sum)[0]);
    }
    while (i < N as usize)
        invariant
            0 <= N,
            N < 1000,
            a.len() == N,
            sum.len() == 1,
            a[(i) as int] <= 2,
            forall|k: usize| k < i ==> sum[0] == old(sum)[0] + a[(k) as int],
            i <= N,
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            sum[0] <= 2 * (i as i32),
    {
        if (i == 0) {
            sum.set(0, old(sum)[0]);
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


//             assert(forall|k: usize| k < i ==> sum[0] == old(sum)[0] + a[(k) as int]);
//   assertion failed: forall|k: usize| k < i ==> sum[0] == old(sum)[0] + a[(k) as int]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False