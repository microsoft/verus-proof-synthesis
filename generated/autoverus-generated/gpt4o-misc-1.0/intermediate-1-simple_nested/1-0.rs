use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| 0 <= k < N ==> #[trigger] b[k] <= k + 1,
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
            0 <= i <= N as usize,
            a.len() == N,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == b[k] + 1 - k,
            forall |k:int| i <= k < N ==> a[k] == old(a)[k],
            N <= sum <= (i as i32) + 2 * (N as i32) - (i as i32),
            sum == (i as i32) + 2 * (N as i32) - (i as i32), // Simplified the expression
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= j <= i,
                a.len() == N,
                b.len() == N,
                a[( i ) as int] == b[( i ) as int] + 1 - j,
                forall |k:int| 0 <= k < i ==> a[k] == b[k] + 1 - k,
                forall |k:int| i <= k < N ==> a[k] == old(a)[k],
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
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 13