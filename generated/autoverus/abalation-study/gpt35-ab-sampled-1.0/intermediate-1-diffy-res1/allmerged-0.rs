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
    let mut i: usize = 0;
    sum.set(0, 0);
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N as usize,
            b.len() == N as usize,
            i <= N as usize,
            0 < N < 1000,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            i <= N,
            sum.len() == 1,
            sum[0] <= 2 * i as i32,
            sum[0] <= 2 * N,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N as usize,
            b.len() == N as usize,
            i <= N as usize,
            0 < N < 1000,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < N ==> a[j] == 1,
            i <= N,
            sum.len() == 1,
            sum[0] <= 2 * N,
            sum[0] == i,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N as usize,
            b.len() == N as usize,
            i <= N as usize,
            0 < N < 1000,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < N ==> a[j] == 1,
            i <= N,
            sum.len() == 1,
            sum[0] <= 2 * N,
            sum[0] == i,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N as usize,
            b.len() == N as usize,
            i <= N as usize,
            0 < N < 1000,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < N ==> a[j] == 1,
            i <= N,
            sum.len() == 1,
            sum[0] <= 2 * N,
            sum[0] == i + N,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 4