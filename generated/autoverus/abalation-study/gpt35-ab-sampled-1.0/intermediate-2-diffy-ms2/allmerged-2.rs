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
            a.len() == N,
            i <= N,
            sum.len() == 1,
            sum[0] <= N,
    {
        a.set(i, i % 2);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            forall|j: int| 0 <= j < i ==> a[j] == j % 2,
            forall|j: int| 1 <= j <= i ==> sum[j - 1] + a[j] >= 0,
            forall|k: int| 0 <= k < i ==> a[k] == k % 2,
            i <= N,
            if (i == 0) {
                sum[0] <= N
            } else {
                sum[0] <= N && sum[0] == old(sum)[0] + a[(i) as int]
            },
            old(a).len() == N,
            old(sum).len() == 1,
            old(sum)[0] <= N,
            sum.len() == 1,
            sum[0] <= N,
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


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 6