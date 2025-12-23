
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
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|j: usize| 0 <= j < i ==> a[(j) as int] == 4,
            i <= N as usize,
            sum.len() == 1,
            N > 0,
            N < 1000,
    {
        a.set(i, 4);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|j: usize| 0 <= j < N as usize ==> a[(j) as int] == 4,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 4 * i,
            N > 0,
            N < 1000,
    {
        if (a[i] == 4) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}

} // verus!

// Score: (3, 0)
// Safe: True