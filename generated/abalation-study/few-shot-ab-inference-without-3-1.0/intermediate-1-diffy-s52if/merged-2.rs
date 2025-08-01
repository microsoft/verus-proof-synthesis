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
        sum[0] == 6 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);
    while (i < N)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            forall|k: int| i <= k < N ==> old(a)[k] == a[k],
            i <= N,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 6,
            forall|k: int| i <= k < N ==> a[k] == 1,
            i <= N,
            sum.len() == 1,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 5);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 6,
            i <= N,
            sum.len() == 1,
            sum[0] == 6 * i,
    {
        if (a[i] == 6) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 2