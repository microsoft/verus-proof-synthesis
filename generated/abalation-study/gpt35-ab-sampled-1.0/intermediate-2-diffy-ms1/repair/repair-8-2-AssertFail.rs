
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
    assert(old(sum)[0] == 0); // Added by AI
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == j % 1,
            i <= N,
            old(a).len() == N,
            old(sum)[0] == 0,
            sum.len() == 1,
            sum[0] == 0, // Added by AI
    {
        a.set(i, i % 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> sum[j] + a[j] == sum[(i) as int],
            i <= N,
            old(a).len() == N,
            sum.len() == 1,
            sum[0] == 0,
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < N ==> a[j] == j % 1,
            forall|j: int| 0 <= j < i ==> sum[j] + a[j] == sum[(i) as int],
            i <= N,
            old(a).len() == N,
            old(sum)[0] == 0,
            sum.len() == 1,
            sum[0] == 0, // Added by AI
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
            proof {
                assert(forall|j: int| 0 <= j < i + 1 ==> sum[j] + a[j] == sum[(i + 1) as int]);
            }
        }
        i = i + 1;
    }
}

} // verus!


//                 assert(forall|j: int| 0 <= j < i + 1 ==> sum[j] + a[j] == sum[(i + 1) as int]);
//   assertion failed: forall|j: int| 0 <= j < i + 1 ==> sum[j] + a[j] == sum[(i + 1) as int]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: True