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
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == k % 1,
            forall|k: int| 0 <= k < i ==> a[k] == k as usize % 1,
            i <= N,
            old(a).len() == N,
            sum.len() == 1,
    {
        a.set(i, i % 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == k % 1,
            forall|k: int| 0 <= k < N ==> a[k] == k as usize % 1,
            i <= N,
            old(a).len() == N,
            sum.len() == 1,
            sum[0] <= old(sum)[0] + (i as usize),
            sum[0] == if i == 0 {
                0
            } else {
                i as usize % 1
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


// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1