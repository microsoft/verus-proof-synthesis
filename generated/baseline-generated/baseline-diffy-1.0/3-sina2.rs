use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] == N + 1,
{
    let mut i: usize = 0;
    sum.set(0, 0);
    
    // Loop to set all elements of a to 1
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < i as int ==> a[k] == 1,
            forall |k:int| i as int <= k < N ==> old(a)[k] == a[k],
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    
    // Loop to accumulate sum of a into sum[0]
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < N ==> a[k] == 1,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    
    // Loop to set all elements of a to N+1
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < i as int ==> a[k] == N + 1,
            sum[0] == N,
            forall |k:int| i as int <= k < N ==> a[k] == 1,
    {
        a.set(i, a[i] + sum[0]);
        i = i + 1;
    }
    
    // Verifying the final condition
    proof {
        assert forall |k:int| 0 <= k < N implies a[k] == N + 1
            by {
                if k < N {
                    assert(a[k] == N + 1);
                }
            };
    }
}
}
// Score: (3, 2)
// Safe: True