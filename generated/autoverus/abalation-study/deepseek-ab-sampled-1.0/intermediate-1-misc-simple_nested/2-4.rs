

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
            sum == seq!(0; i as i32).map(|k| b[k as usize] + 1 -k).sum(),
            forall |k: usize| k < i ==> a[k] == b[k] as i32 + 1 -k as i32,
        aman  
        {
            This ensures that for each completed iteration:
                a[k] is correctly computed as b[k] + 1 - k
                sum is accumulating correctly as per a's values.
        }
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant 
                j <= i,
                a[i] == b[i] + 1 - j as i32,
                b.len() == N,
                a.len() == N,
            aman
            {
                Tracks a[i] decrementing exact j times.
            }
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2