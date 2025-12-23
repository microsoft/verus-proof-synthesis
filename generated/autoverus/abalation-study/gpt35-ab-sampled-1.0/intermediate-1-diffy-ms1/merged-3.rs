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
            forall|j: int| 0 <= j < i ==> a[j] == j % 1,
            i <= N,
            i <= N as usize,
            old(a).len() == N,
            old(sum)[0] == 0,
            sum.len() == 1,
    {
        a.set(i, i % 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == j % 1,
            i <= N,
            i <= N as usize,
            if (i == 0) {
                sum[0] == 0
            } else {
                sum[0] == old(sum)[0] + a[i - 1]
            },
            old(a).len() == N,
            old(sum).len() == 1,
            old(sum)[0] == 0,
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