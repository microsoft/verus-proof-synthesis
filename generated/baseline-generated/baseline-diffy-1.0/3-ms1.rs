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
    while i < N
        invariant
            0 <= i <= N,
            a@.len() == N,
            forall |j: int| 0 <= j < i ==> a[j] == j % 1,
    {
        a.set(i, i % 1);
        i = i + 1;
    }

    i = 0;
    sum.set(0, 0);
    
    while i < N
        invariant
            0 <= i <= N,
            sum@.len() == 1,
            forall |j: int| 0 <= j < i ==> a[j] == j % 1,
            sum[0] == 0,
    {
        sum.set(0, 0);
        i = i + 1;
    }
}
}
// Score: (2, 1)
// Safe: False