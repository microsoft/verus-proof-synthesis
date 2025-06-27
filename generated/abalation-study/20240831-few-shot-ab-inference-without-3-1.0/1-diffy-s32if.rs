use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    
    // Invariant for the first loop
    while (i < N)
        invariant
            i <= N,
            a.len() == N,
            N < 1000,
            forall |k:int| 0 <= k < i ==> a[k] == 1,
            forall |k:int| i <= k < N ==> old(a)[k] == a[k],
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    
    // Invariant for the second loop
    while (i < N)
        invariant
            i <= N,
            a.len() == N,
            N < 1000,
            forall |k:int| 0 <= k < i ==> (a[k] == 4),
            forall |k:int| i <= k < N ==> (a[k] == 1),
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    
    // Invariant for the third loop
    while (i < N)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            N < 1000,
            sum[0] == 4 * (i as i32), // This ensures the sum invariant
            forall |k:int| 0 <= k < i ==> a[k] == 4,
            forall |k:int| i <= k < N ==> a[k] == 4,
    {
        if (a[i] == 4) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}
}
// Score: (4, 0)
// Safe: True