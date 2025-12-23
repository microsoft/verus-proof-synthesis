

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
            // Sum of a[0..i] is sum
            sum == a@.take(( i ) as int).sum(),
            // Remaining elements to process is N - i
            N as usize - i <= N as usize,
        {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i) 
            invariant 
                // After inner loop, a[i] == b[i] + 1 - j
                a[i] == b[i] + 1 - (j as i32),
                // Correlating a and b after each adjustment
                a[i] == b[i] + 1 - j as i32,
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5