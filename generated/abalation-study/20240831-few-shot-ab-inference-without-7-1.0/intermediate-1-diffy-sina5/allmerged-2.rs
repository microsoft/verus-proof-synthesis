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
        forall|k: int| 0 <= k < N ==> a[k] == 2 * N + 1,
{
    let mut i: usize = 0;
    sum.set(0, 0);
    while (i < N as usize)
        invariant
            a.len() == N,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            forall|j: int| i <= j < N ==> a[j] == old(a)[j],
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N,
            i <= N as usize,
            sum.len() == 1,
            old(a).len() == N,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N as usize,
            b.len() == N,
            b.len() == N as usize,
            forall|j: int| 0 <= j < i ==> b[j] == 1,
            forall|j: int| i <= j < N ==> b[j] == old(b)[j],
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            i <= N,
            i <= N as usize,
            sum.len() == 1,
            old(b).len() == N,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|j: int| 0 <= j < N ==> a[j] == 1,
            forall|k: int| 0 <= k < N as usize ==> b[k] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= i,
            sum[0] as int == i,
            old(a).len() == N,
            old(sum).len() == 1,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            b.len() == N,
            forall|j: int| 0 <= j < N ==> b[j] == 1,
            forall|k: int| 0 <= k < N as usize ==> b[k] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 2 * i as i32,
            sum[0] as int == N + i,
            old(b).len() == N,
            old(sum).len() == 1,
            sum[0] == N + i as i32,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 2 * N + 1,
            forall|j: int| i <= j < N ==> a[j] == 1,
            forall|k: int| 0 <= k < N as usize ==> b[k] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 2 * N + 1,
            i <= N,
            i <= N as usize,
            sum.len() == 1,
            sum[0] >= 2 * N,
            sum[0] as int == 2 * N,
            old(a).len() == N,
            old(sum).len() == 1,
            sum[0] == 2 * N,
    {
        a.set(i, a[i] + sum[0]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 5, Errors: 1, Verus Errors: 1