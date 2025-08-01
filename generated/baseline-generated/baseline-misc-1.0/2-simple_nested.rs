use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| 0 <= k < N ==> b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N
{  
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    
    while (i < N as usize)
    invariant
        0 <= i <= N,
        forall |k: int| 0 <= k < i ==> a[k] == 1,
        sum == i,
        a.len() == N,
        b.len() == N,
        forall |k:int| 0 <= k < N ==> b[k] <= k + 1
    {
        a.set(i, b[i] + 1);

        let mut j: usize = 0;
        
        while (j < i)
        invariant
            0 <= j <= i,
            sum == i,
            a.len() == N,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == 1
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
// Score: (1, 5)
// Safe: False