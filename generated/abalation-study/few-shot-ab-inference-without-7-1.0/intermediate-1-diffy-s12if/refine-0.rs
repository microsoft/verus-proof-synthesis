
use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N)
        invariant
            0 <= i <= N,
            a.len() == N,
            a@.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            forall|j: nat| j < i ==> a[(j) as int] == 1,
            i <= N,
            sum.len() == 1,
            sum@.len() == 1,
            sum[0] == 0,
            N > 0,
            N < 1000,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            0 <= i <= N,
            a.len() == N,
            a@.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 2,
            forall|j: int| i <= j < N ==> a[j] == 1,
            forall|j: nat| j < i ==> a[(j) as int] == 2,
            i <= N,
            sum.len() == 1,
            sum@.len() == 1,
            sum[0] == 0,
            N > 0,
            N < 1000,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 1);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            0 <= i <= N,
            0 <= sum[0] <= 2 * i,
            a.len() == N,
            a@.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 2,
            forall|j: nat| j < i ==> a[(j) as int] == 2,
            i <= N,
            sum.len() == 1,
            sum@.len() == 1,
            sum[0] == 2 * i,
            sum[0] <= 2 * i,
            N > 0,
            N < 1000,
    {
        if (a[i] == 2) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}

} // verus!

