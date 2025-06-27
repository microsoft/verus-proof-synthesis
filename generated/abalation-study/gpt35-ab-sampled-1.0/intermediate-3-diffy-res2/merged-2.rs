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
            forall|j: int| 0 <= j < i ==> a[j] == 1,
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
            N < 1000,
            N > 0,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            a.len() == N,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < i ==> b[j] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            forall|j: int| 0 <= j < i ==> b[j] == 1,
            a.len() == N,
            b.len() == N,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            forall|j: int| 0 <= j < i ==> c[j] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
    {
        c.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            forall|j: int| 0 <= j < i ==> c[j] == 1,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 4, Errors: 3, Verus Errors: 10