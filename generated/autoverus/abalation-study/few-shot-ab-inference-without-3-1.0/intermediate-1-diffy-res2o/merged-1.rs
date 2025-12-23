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
            a.len() == N,
            i <= N,
            forall|k: int| 0 <= k < i as int ==> a[k] == 1,
            forall|k: int| i as int <= k < N as int ==> a[k] == old(a)[k],
            i <= N as usize,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            b.len() == N,
            i <= N,
            forall|k: int| 0 <= k < i as int ==> b[k] == 1,
            forall|k: int| i as int <= k < N as int ==> b[k] == old(b)[k],
            i <= N as usize,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            c.len() == N,
            i <= N,
            forall|k: int| 0 <= k < i as int ==> c[k] == 1,
            forall|k: int| i as int <= k < N as int ==> c[k] == old(c)[k],
            i <= N as usize,
    {
        c.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            i <= N,
            forall|k: int| 0 <= k < i as int ==> a[k] == 1,
            forall|k: int| i as int <= k < N as int ==> a[k] == 1,
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
            b.len() == N,
            i <= N,
            forall|k: int| 0 <= k < i as int ==> b[k] == 1,
            forall|k: int| i as int <= k < N as int ==> b[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= N + i,
            sum[0] <= N + i as i32,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            c.len() == N,
            i <= N,
            forall|k: int| 0 <= k < i as int ==> c[k] == 1,
            forall|k: int| i as int <= k < N as int ==> c[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 2 * N + i,
            sum[0] <= 2 * N + i as i32,
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 5, Errors: 2, Verus Errors: 2