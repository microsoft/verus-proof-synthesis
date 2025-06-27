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
            b.len() == N,
            c.len() == N,
            forall|j: usize| j < i ==> a[(j) as int] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            forall|j: usize| j < i ==> a[(j) as int] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N,
            sum.len() == 1,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            forall|j: usize| j < i ==> b[(j) as int] == 1,
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            i <= N,
            sum.len() == 1,
            sum[0] == N + i as i32,
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
            c.len() == N,
            forall|j: usize| j < i ==> b[(j) as int] == 1,
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            i <= N,
            sum.len() == 1,
            sum[0] == N + i as i32,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            a.len() == N,
            b.len() == N,
            c.len() == N,
            forall|j: usize| j < i ==> c[(j) as int] == 1,
            forall|k: int| 0 <= k < i ==> c[k] == 1,
            i <= N,
            sum.len() == 1,
            sum[0] == 2 * N + i as i32,
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
            forall|j: usize| j < i ==> c[(j) as int] == 1,
            forall|k: int| 0 <= k < i ==> c[k] == 1,
            i <= N,
            sum.len() == 1,
            sum[0] == 2 * N + i as i32,
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 2, Errors: 5, Verus Errors: 14