
use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| k <= b[k] <= k + 1,
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
            0 <= i <= b.len(),
            a.len() == N as usize,
            sum == a.subrange(0, i as int).fold(0, |acc, x| acc + x),
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                j <= i,
                a.len() == N as usize,
                0 <= j < i,
                a.subrange(0, i as int).filter(|k| k == i as i32).count() == 1,
                a.subrange(0, i as int).filter(|k| k == i as i32 - 1).count() == j as i32,
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3