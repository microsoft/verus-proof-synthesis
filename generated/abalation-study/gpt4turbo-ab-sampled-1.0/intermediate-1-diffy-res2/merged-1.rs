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
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            i <= N as usize,
            sum.len() == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            a.len() == N,
            forall|j: int| 0 <= j < N ==> a[j] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == i,
            b.len() == N,
            i <= N,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            b.len() == N,
            forall|j: int| 0 <= j < i ==> b[j] == 1,
            i <= N as usize,
            sum.len() == 1,
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            i <= N,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < N ==> b[j] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == N + i,
            c.len() == N,
            i <= N,
            sum[0] == N + i as i32,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            c.len() == N,
            forall|j: int| 0 <= j < i ==> c[j] == 1,
            i <= N as usize,
            sum.len() == 1,
            forall|k: int| 0 <= k < i ==> c[k] == 1,
            i <= N,
    {
        c.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            forall|j: int| 0 <= j < N ==> c[j] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 2 * N + i,
            i <= N,
            sum[0] == 2 * N + i as i32,
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 7, Errors: 0, Verus Errors: 0