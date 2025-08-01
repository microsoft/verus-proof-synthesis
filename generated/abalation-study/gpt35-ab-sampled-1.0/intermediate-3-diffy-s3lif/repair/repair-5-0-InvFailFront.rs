
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 < N,
            N > 0,
            a.len() == N as usize,
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == 4 * (i as i32),
            N < 1000,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N,
            N > 0,
            a.len() == N as usize,
            forall|j: int| 0 <= j < i ==> (a[j] == 1),
            forall|j: int| i <= j < N as usize ==> (a[j] == 0),
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == 4 * N,
            N < 1000,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N,
            N > 0,
            a.len() == N as usize,
            forall|j: int| 0 <= j < i ==> a[j] != 1,
            forall|j: int| i <= j < N as usize ==> a[j] == 0, // Fixing the failed invariant
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == 4 * (i as i32),
            sum[0] == 4 * N,
            N < 1000,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
} // verus!


//             forall|j: int| i <= j < N as usize ==> (a[j] == 0),
//   None: forall|j: int| i <= j < N as usize ==> (a[j] == 0)

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True