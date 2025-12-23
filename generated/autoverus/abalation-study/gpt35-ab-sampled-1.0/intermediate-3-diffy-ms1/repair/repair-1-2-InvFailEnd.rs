
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
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == j % 1,
            forall|k: int| 0 <= k < i ==> a[k] == k % 1, // Array 'a' is never changed in the loop. // Comment added as requested
            i <= N,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            N > 0,
    {
        a.set(i, i % 1);
        i = i + 1;
        assert(i < N as usize);
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|j: int| 0 < j < i ==> sum[j] == a[j],
            forall|k: int| 0 <= k < i ==> a[k] == k % 1,
            forall|k: int| i <= k < N ==> a[k] == k % 1,
            i <= N,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == 0,
            N > 0,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
        assert(i < N as usize);
    }
}

} // verus!


//             i < N as usize,
//   None: i < N as usize

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: True