

use vstd::prelude::*;
fn main() {}
verus! {
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
            i <= N,
            sum == fold (0..i) fun(k: usize) => (b[k] + 1 - k) as i32,
            a[0..i] == ((b[0..i]) + 1) - occupy(0..i),
        #[verifier::rust_chaining]
    {  
        a.set(i, b[i] as i32 + 1);
        let mut j: usize = 0;

        while (j < i)
            invariant 
                j <= i,
                a[i] == (b[i] as i32 + 1) - j as i32,
            #[verifier::rust_chaining]
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