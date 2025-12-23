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
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            i <= N,
            sum.len() == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N as usize,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < i ==> b[j] == 1,
            i <= N,
            sum.len() == 1,
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            i <= N as usize,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < N ==> a[j] == 1,
            forall|j: int| 0 <= j < N ==> b[j] == 1,
            i <= N,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == i,
            sum[0] <= i as i32 * 1,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < N ==> b[j] == 1,
            forall|j: int| 0 <= j < i ==> a[j] == N + 1,
            i <= N,
            forall|k: int| 0 <= k < i ==> a[k] == N + 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == N,
    {
        a.set(i, b[i] + sum[0]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 4, Errors: 1, Verus Errors: 3