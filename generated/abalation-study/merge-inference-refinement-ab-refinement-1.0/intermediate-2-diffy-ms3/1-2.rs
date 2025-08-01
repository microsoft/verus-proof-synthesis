use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            old(sum).len() == 1,
            N > 0,
            N < 1000,
            forall |k: int| 0 <= k < i ==> a[k as int] == (k % 3) as i32,
            forall |k: int| 0 <= k < N ==> a.len() == N, // Array length is unchanged
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            forall |k: int| 0 <= k < N ==> a[k as int] == (k % 3) as i32,
            i > 0 ==> sum[0] <= 2 * i as i32, // Conditional loop invariant refinement
            forall |k: int| 0 <= k < N ==> a.len() == N,  // Array length is unchanged
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1