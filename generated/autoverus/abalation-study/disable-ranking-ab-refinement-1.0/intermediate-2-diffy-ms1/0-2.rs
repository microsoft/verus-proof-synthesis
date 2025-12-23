use vstd::prelude::*;
fn main() {}
verus!{

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
            i <= N,
            a.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < i ==> a[k] == (k % 1),
    {
        a.set(i, i % 1 );
        i = i + 1;
    }

    i = 0;

    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < N ==> a[k] == (k % 1),
            sum[0] <= i, // since a[k] is 0 or 1, the maximum sum would be i (when all entries in a are 1)
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2