use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] == 0,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == j % 1,
            forall|k: int| 0 <= k < i ==> a[k] == k % 1,
            i <= N,
            old(a).len() == N,
            old(sum)[0] == 0,
            sum.len() == 1,
            sum[0] == if (i == 0) {
                0
            } else {
                sum[0] + a[i - 1]
            },
    {
        a.set(i, i % 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < N ==> a[j] == j % 1,
            forall|j: int| 0 <= j < i ==> sum[j] + a[j] == sum[(i) as int],
            i <= N,
            old(a).len() == N,
            if i == 0 {
                sum[0] == 0
            } else {
                sum[0] == old(sum)[0] + old(a)[(i) as int]
            },
            sum.len() == 1,
            sum[0] == 0,
            sum[0] == if (i == 0) {
                0
            } else {
                sum[0] + a[(i) as int]
            },
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


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5