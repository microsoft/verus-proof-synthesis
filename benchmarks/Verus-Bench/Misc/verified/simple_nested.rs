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
            0 <= i <= N,
            N <= 0x3FFF_FFFF,
            a.len() == N,  // always specify the length of vectors used in the loop
            b.len() == N,  // always specify the length of vectors used in the loop
            forall |k:int| k <= #[trigger] b[k] <= k + 1,
            i <= sum <= 2*i,
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant 
                0 <= i < N,
                0 <= j <= i,
                a.len() == N,  // always specify the length of vectors used in the loop
                i + 1 - j <= a[i as int] <= i + 2 - j,
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
