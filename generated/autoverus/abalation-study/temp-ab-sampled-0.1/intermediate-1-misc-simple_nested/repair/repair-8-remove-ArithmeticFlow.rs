use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
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
            a.len() == N,
            b.len() == N,
            i <= N as usize,
            forall |k: usize| k < i ==> a[( k ) as int] >= 1, // Ensure a[k] is at least 1 before decrement
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                N <= 0x3FFF_FFFF,
                a.len() == N,
                b.len() == N,
                j <= i,
                a[( i ) as int] >= j + 1, // Ensure a[i] is at least j + 1 before decrement
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        i = i + 1;
    }  
    sum
}
}
