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
        forall|k: int| 0 <= k < N ==> a[k] == N + 1,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N as int,
            b.len() == N as int,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N as usize,
            0 < N,
            N < 1000,
            a.len() == b.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == b[k] + sum[0],
            sum.len() == 1,
            sum[0] == 0,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N as int,
            b.len() == N as int,
            0 < N,
            N < 1000,
            a.len() == b.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 0,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N as int,
            b.len() == N as int,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            forall|k: int| 0 <= k < N ==> b[k] == 1,
            i <= N as usize,
            N < 1000,
            a.len() == b.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N,
            sum.len() == 1,
            sum[0] == i,
            sum[0] == (i as i32),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N as int,
            b.len() == N as int,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            forall|k: int| 0 <= k < N ==> b[k] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == b[k] + sum[0],
            i <= N as usize,
            N < 1000,
            a.len() == b.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == b[k] + N + 1,
            i <= N,
            sum.len() == 1,
            sum[0] == N,
            sum[0] == (N as i32),
    {
        a.set(i, b[i] + sum[0]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 3