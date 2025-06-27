use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] == 0,
{
    sum.set(0, 0);
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            forall |j:int| 0 <= j < i ==> a[j] == 1,
            forall |j:int| i <= j < N ==> a[j] == old(a)[j],
            N > 0,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            sum.len() == 1,
            a.len() == N,
            N > 0,
            sum[0] == i as i32,
            forall |j:int| 0 <= j < i ==> a[j] == 1,
            forall |j:int| i <= j < N ==> a[j] == 1,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            N > 0,
            sum[0] == N,
            forall |j:int| 0 <= j < i ==> a[j] == 0,
            forall |j:int| i <= j < N ==> a[j] == 0 || a[j] == 1,
    {
        if (sum[0] == N) {
            a.set(i, a[i] - 1);
        } else {
            a.set(i, a[i] + 1);
        }
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1