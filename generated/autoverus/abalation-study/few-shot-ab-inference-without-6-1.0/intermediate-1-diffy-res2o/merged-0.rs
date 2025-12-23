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
    let mut i: usize = 0;
    sum.set(0, 0);
    while (i < N as usize)
        invariant
            0 <= i <= N,
            N > 0 && N < 1000,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N as usize,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            N > 0 && N < 1000,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            i <= N as usize,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            N > 0 && N < 1000,
            c.len() == N,
            forall|k: int| 0 <= k < i ==> c[k] == 1,
            i <= N as usize,
    {
        c.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= i + 2 * N,
            sum[0] <= (3 * i) as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            b.len() == N,
            forall|k: int| 0 <= k < N ==> b[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= N + i + N,
            sum[0] <= (3 * i + N) as i32,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            c.len() == N,
            forall|k: int| 0 <= k < N ==> c[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 2 * N + i + N,
            sum[0] <= (3 * i + 2 * N) as i32,
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 3, Errors: 4, Verus Errors: 10