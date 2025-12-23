use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(c).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            forall|k: int| 0 <= k < i as int ==> a[k as int] == 1,
            i <= N as usize,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            forall|k: int| 0 <= k < i as int ==> a[k as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= i,
            sum[0] <= i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            forall|k: int| 0 <= k < i as int ==> b[k as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= N,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            b.len() == N,
            forall|k: int| 0 <= k < N ==> b[k] == 1,
            forall|k: int| 0 <= k < i as int ==> b[k as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 2 * N,
            sum[0] <= (N + i as i32),
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            c.len() == N,
            forall|k: int| 0 <= k < i ==> c[k] == 1,
            forall|k: int| 0 <= k < i as int ==> c[k as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 2 * N,
    {
        c.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            c.len() == N,
            forall|k: int| 0 <= k < N ==> c[k] == 1,
            forall|k: int| 0 <= k < i as int ==> c[k as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
            sum[0] <= (2 * N + i as i32),
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}

} // verus!


// Score: (7, 0)
// Safe: True