
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
            forall|j: int| 0 <= j < i ==> a[j] == j % 1,
            i <= N,
            i <= N as usize,
            old(a).len() == N,
            old(sum)[0] == 0,
            sum.len() == 1,
    {
        a.set(i, i % 1);
        i = i + 1;
    }
    i = 0;
    proof {
        assert(old(sum)[0] == 0);
    } // Added by AI
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == j % 1,
            i <= N,
            i <= N as usize,
            if (i == 0) {
                sum[0] == 0
            } else {
                sum[0] == old(sum)[0] + a[i - 1]
            },
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
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


//             old(sum)[0] == 0,
//   None: old(sum)[0] == 0

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: True