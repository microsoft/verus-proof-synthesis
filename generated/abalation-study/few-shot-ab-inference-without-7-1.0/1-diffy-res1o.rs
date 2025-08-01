
use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            i <= N,
            forall|j: usize| 0 <= j < i ==> a[(j) as int] == 1,
            i <= N as usize,
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
            forall|j: int| 0 <= j < N ==> a[j] == 1,
            i <= N,
            forall|j: usize| 0 <= j < i ==> a[(j) as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= i as i32,
            sum[0] <= N,
            N > 0,
            N < 1000,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            b.len() == N,
            forall|j: int| 0 <= j < i ==> b[j] == 1,
            i <= N,
            forall|j: usize| 0 <= j < i ==> b[(j) as int] == 1,
            i <= N as usize,
            N > 0,
            N < 1000,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            b.len() == N,
            forall|j: int| 0 <= j < N ==> b[j] == 1,
            i <= N,
            forall|j: usize| 0 <= j < i ==> b[(j) as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= N + i as i32,
            sum[0] <= 2 * N,
            N > 0,
            N < 1000,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
}

} // verus!

// Score: (5, 0)
// Safe: True