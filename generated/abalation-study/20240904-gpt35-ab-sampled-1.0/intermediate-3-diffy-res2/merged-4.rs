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
            0 < N < 1000,
            N < 1000,
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            i <= N,
            a.len() == N as usize,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
            sum[0] >= 0,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N < 1000,
            N < 1000,
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            i <= N,
            a.len() == N as usize,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
            sum[0] == i as i32,
            sum[0] <= 1 * i,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N < 1000,
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < i ==> b[j] == 1,
            i <= N,
            a.len() == N as usize,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
            sum[0] <= 2 * i,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N < 1000,
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < i ==> b[j] == 1,
            i <= N,
            a.len() == N as usize,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
            sum[0] <= 3 * i,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N < 1000,
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            forall|j: int| 0 <= j < i ==> c[j] == 1,
            i <= N,
            a.len() == N as usize,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
            sum[0] <= 4 * i,
    {
        c.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N < 1000,
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            forall|j: int| 0 <= j < i ==> c[j] == 1,
            i <= N,
            a.len() == N as usize,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
            sum[0] <= 5 * i,
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 3, Errors: 4, Verus Errors: 17