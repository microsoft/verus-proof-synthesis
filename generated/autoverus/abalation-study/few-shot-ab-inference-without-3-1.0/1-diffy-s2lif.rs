
use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < i as int ==> a[k] == 1,
            forall|k: int| i as int <= k < N ==> old(a)[k] == a[k],
            i <= N as usize,
            sum.len() == 1,
            N > 0,
            N < 1000,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < i as int ==> a[k] == 3,
            forall|k: int| i as int <= k < N ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            N > 0,
            N < 1000,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 2);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 3,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == i as i32 * 3,
            N > 0,
            N < 1000,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}

} // verus!

// Score: (4, 0)
// Safe: True