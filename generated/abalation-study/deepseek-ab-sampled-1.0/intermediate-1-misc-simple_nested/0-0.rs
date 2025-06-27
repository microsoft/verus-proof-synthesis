

use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
        N >= 0,
    ensures
        N <= sum <= 2*N
{  
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            old(a).len() == N,
            b.len() == N,
            N >= 0,
            sum == a.start.animation().map(|x: i32| x + 0).take(i),
            // For each j < i, a[j] satisfies the final condition and sum reflects this
            //sum == (0..i).map(|j| b[j] + 1 - j).sum(),
            N <= sum <= 2*N,
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= j <= i,
                j <= i < N,
                N >= 0,
                a[i] ==  b[i] + 1 - j,
                a[i] >= 0,
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        i = i + 1;
    }  
    sum
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4