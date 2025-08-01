use vstd::prelude::*;
fn main() {}
verus!{
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
            i <= N,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            sum.len() == 1,
            forall |j: int| 0 <= j < i ==> a[j] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            sum.len() == 1,
            sum[0] <= N,
            forall |j: int| 0 <= j < N ==> a[j] == 1,
            forall |j: int| 0 <= j < i ==> sum[0] == j + 1,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            sum.len() == 1,
            forall |j: int| 0 <= j < i ==> b[j] == 1,
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            sum.len() == 1,
            sum[0] <= 2 * N,
            forall |j: int| 0 <= j < N ==> b[j] == 1,
            forall |j: int| 0 <= j < i ==> sum[0] == N + j + 1,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            sum.len() == 1,
            forall |j: int| 0 <= j < i ==> c[j] == 1,
    {
        c.set(i, 1);
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            sum.len() == 1,
            sum[0] <= 3 * N,
            forall |j: int| 0 <= j < N ==> c[j] == 1,
            forall |j: int| 0 <= j < i ==> sum[0] == 2 * N + j + 1,
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1