use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| 0 <= #[trigger] b[k] <= k + 1,
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
            forall |k: int| 0 <= k < i as int ==> a[k] == b[k] + 1 - k,
            0 <= sum,
            sum <= 2 * i as i32,
            implies(forall |k: int| 0 <= k < N ==> 0 <= b[k] <= k + 1),
    {  
        a.set(i, b[i] + 1);
        
        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= j <= i,
                a.len() == N,
                a[i] == b[i] + 1 - j,
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