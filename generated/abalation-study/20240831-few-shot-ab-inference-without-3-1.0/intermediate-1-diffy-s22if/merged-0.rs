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
        sum[0] == 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N)
        invariant
            N < 1000,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            forall|k: int| i <= k < N ==> a[k] == old(a)@.index(k),
            i <= N,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            N < 1000,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 3,
            forall|k: int| i <= k < N ==> a[k] == 1,
            i <= N,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 2);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N)
        invariant
            N < 1000,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 3,
            forall|k: int| 0 <= k < i ==> a[k] == 3,
            i <= N,
            sum.len() == 1,
            sum[0] <= 3 * i,
            sum[0] == 3 * i,
    {
        if (a[i] == 3) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 4, Errors: 0, Verus Errors: 0