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
    
    // First loop: set all elements of `a` to 0 (since i % 1 == 0 for all i)
    while i < N 
        invariant
            0 <= i <= N,
            a@.len() == N, 
            forall |k:int| 0 <= k < i ==> a[k] == 0,
            forall |k:int| i <= k < N ==> a[k] == old(a)[k],
    {
        a.set(i, i % 1 );
        i = i + 1;
    }

    i = 0;

    // Second loop: set sum[0] to 0
    while i < N 
        invariant
            0 <= i <= N,
            sum@.len() == 1,
            forall |k:int| 0 <= k < i ==> a[k] == 0,
            forall |k:int| i <= k < N ==> a[k] == 0,
            if i == 0 { sum[0] == old(sum)[0] } else { sum[0] == 0 },
    {
        if i == 0 {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        assert(sum[0] == 0);  // Added assertion since sum[0] + a[i] will always be 0
        i = i + 1;
    }
}
}
// Score: (2, 1)
// Safe: False