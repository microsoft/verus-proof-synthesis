

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
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            forall |j:int| 0 <= j < i as int ==> b[j] == a[j] - 1,
            0 <= N as usize <= 0x3FFF_FFFF,
            a@ == old(a@).take(i as int),
            sum == a@.take(i as int).sum(),
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                j <= i,
                a.len() == N,
                b.len() == N,
                a[i] == b[i] + 1 - j as i32,
                i <= N as usize,
                0 <= i as int,
                0 <= j as int,
                a@.take(i as int) == old(a@).take(i as int),
                sum == a@.take(i as int).sum(),
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4