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
            forall|k: int| 0 <= k < i ==> a[k] == k as usize % 2,
            i <= N,
            sum.len() == 1,
            N > 0,
    {
        a.set(i, i % 2);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < a.len() ==> a[k] == k as usize % 2,  // This is added to ensure invariant covers every element in array 'a'
            i <= N,
            (i > 0 ==> 0 <= sum[0] <= i),  // Changed to conditional invariant for i > 0 iteration
            sum.len() == 1,
            N > 0,
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

// Score: (3, 0)
// Safe: True