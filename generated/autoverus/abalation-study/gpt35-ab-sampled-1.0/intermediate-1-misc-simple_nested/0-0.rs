
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
            i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            sum >= 0,
            // Add your additional invariants here, if any
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                j <= i,
                b.len() == N as usize,
                a.len() == N as usize,
                forall |k:int| 0 <= k < j ==> a[k] == b[k] + 1,
                sum >= 0,
                // Add your additional invariants here, if any
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

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 9