

use vstd::prelude::*;
fn main() {}

verus! {
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| k <= #[trigger] b[k] <=k +1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <=2*N
{  
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize) 
        invariant 
            N <= 0x3FFF_FFFF,
            i <= N,
            a.len() == N,
            b.len() == N,
            sum == a@.take(i as int).sum(),
            forall |k:int| 0 <= k <i as int ==> a[k] == b[k] +1 - (k as int),
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant 
                j <=i,
                a.len() ==N,
                b.len() ==N,
                a[i] == b[i] +1 -j as int,
        {
            a.set(i, a[i] -1);
            j = j +1;
        }
        sum = sum + a[i];
        i = i +1;
    }
    sum
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3