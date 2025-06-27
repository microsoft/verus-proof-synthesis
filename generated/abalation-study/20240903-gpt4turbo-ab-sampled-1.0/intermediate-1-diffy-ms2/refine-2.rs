
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
            a.len() == N, // specifying the length of the array `a`
            forall|k: int| 0 <= k < i ==> a[k] == k % 2, // Loop modifies a, so invariant is appropriate as it progressively checks modified elements.
            i <= N,
            sum.len() == 1, // specifying the length of the array `sum`
    {
        a.set(i, i % 2);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N, // specifying the length of the array `a`
            // No a.set() in this loop, hence covering every element in a is needed. We believe the related array is never changed in this loop because the loop operation focuses on sum rather than modifying `a`.
            forall|k: int| 0 <= k < N ==> a[k] == k % 2, 
            i <= N,
            if i == 0 {
                sum[0] == 0
            } else {
                sum[0] <= i && sum[0] <= N
            },
            // Invariant covers every element of sum, no modification of sum's structure, hence no adjustment needed.
            sum.len() == 1, // specifying the length of the array `sum`
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
