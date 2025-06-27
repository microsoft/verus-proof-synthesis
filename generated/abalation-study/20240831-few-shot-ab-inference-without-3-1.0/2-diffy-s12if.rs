
use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 2,
            forall|k: int| i <= k < N ==> a[k] == 1,
            i <= N,
            sum.len() == 1,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 1);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            // Since no a.set() is called in this loop, the invariant should check every element in the array.
            forall|k: int| 0 <= k < a.len() ==> a[k] == 2,
            i <= N,
            sum.len() == 1,
            sum[0] == 2 * i,
    {
        if (a[i] == 2) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}

} // verus!

// Score: (4, 0)
// Safe: True