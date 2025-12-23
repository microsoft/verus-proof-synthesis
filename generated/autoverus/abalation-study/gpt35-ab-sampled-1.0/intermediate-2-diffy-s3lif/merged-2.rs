use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            0 < N,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N,
            forall|j: usize| 0 <= j < i ==> a[(j) as int] == 1,
            forall|j: usize| i <= j < N ==> a[(j) as int] == 0,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == 0,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            0 < N,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> ((a[k] == 4) || (a[k] == 0)),
            i <= N,
            forall|j: usize| 0 <= j < N ==> (a[(j) as int] == 1 || a[(j) as int] == 0),
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == 0,
            sum[0] == 3 * i,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            0 < N,
            a.len() == N,
            i <= N,
            forall|j: usize| 0 <= j < i ==> (a[(j) as int] == 4 || a[(j) as int] == 3),
            forall|j: usize| i <= j < N ==> (a[(j) as int] == 3 || a[(j) as int] == 2),
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == 4 * i,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 6