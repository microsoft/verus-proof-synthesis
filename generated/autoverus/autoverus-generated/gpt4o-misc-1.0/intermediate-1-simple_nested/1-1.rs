use vstd::prelude::*;
fn main() {}
verus!{
pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires 
        forall |k:int| k < N ==> b[k as int] <= k + 1,
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
            0 <= i as int <= N,
            sum <= i as int,
            forall |k:int| 0 <= k < i as int ==> a[k as int] == if k == 0 { b[0] + 1 } else { 1 + b[k as int] } - k,
            forall |k:int| 0 <= k < i as int ==> b[k as int] <= k + 1,
            0 <= sum <= 2*i as int,
            a.len() == N,
            b.len() == N,
            old(a).len() == N,
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= j as int <= i as int,
                a[( i ) as int] == b[( i ) as int] + 1 - j as int,
                a.len() == N,
                b.len() == N,
                old(a).len() == N,
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
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 11