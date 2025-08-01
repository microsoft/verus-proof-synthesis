use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == j % 2,
            forall|k: int| 0 <= k < i ==> a[k] == k % 2,
            i <= N,
            sum.len() == 1,
    {
        a.set(i, i % 2);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            (sum[0] <= i) || (i == 0 && sum[0] == 0),
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < N ==> a[j] == j % 2,
            forall|k: int| 0 <= k < N ==> a[k] == k % 2,
            i <= N,
            forall|k: int| 0 <= k < i ==> a[k] == k % 2,
            i <= N as usize,
            i == 0 ==> sum[0] == 0,
            i > 0 ==> sum[0] == sum[0] + sum[i - 1],
            i > 0 ==> sum[0] <= N,
            sum.len() == 1,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3