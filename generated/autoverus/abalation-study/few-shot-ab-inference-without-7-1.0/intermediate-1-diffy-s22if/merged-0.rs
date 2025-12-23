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
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
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
            forall|j: int| 0 <= j < i ==> a[j] == 3,
            forall|j: int| i <= j < N ==> a[j] == 1,
            i <= N,
            sum.len() == 1,
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
            a.len() == N,
            forall|j: int| 0 <= j < N ==> a[j] == 3,
            i <= N,
            sum.len() == 1,
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


// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 2