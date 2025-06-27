
use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| k <= #[trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2*N
{  
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize) 
        invariant
            N <= 0x3FFF_FFFF,
            b.len() == N,
            old(a).len() == N,
            0 <= i <= N,
            forall |k:int| k < i ==> a[k] + 1 == b[k],
            sum == a[0] + a[1] + ... + a[i-1],
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= j <= i,
                0 <= i <= N,
                b.len() == N,
                old(a).len() == N,
                forall |k:int| k < j ==> a[k] + 1 == b[k],
                a[i] + sum == a[0] + a[1] + ... + a[i-1],
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1