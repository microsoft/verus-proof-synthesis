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
    let mut temp_sum: i32 = 0; // Temporary partial sum for clarity and to capture intention more accurately.
    while (i < N as usize) 
        invariant
            i <= N as usize,
            b.len() == N,
            a.len() == N,
            0 <= sum, // Encourage clarity of intention through invariant.
            sum == temp_sum, // Relate sum to the evolving temporary sum.
            N <= 0x3FFF_FFFF,
            forall |k:int| k <= b[k] <= k + 1,
            forall |k:int| 0 <= k < i as int ==> a[k] == b[k], // Reflect the current state of a relative to b and iterations made.
            0 <= temp_sum <= 2*i as i32, // Temporary partial sum constraints.
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                j <= i,
                i <= N as usize,
                b.len() == N,
                a.len() == N,
                0 <= sum,
                sum == temp_sum,
                N <= 0x3FFF_FFFF,
                forall |k:int| k <= b[k] <= k + 1,
                forall |k:int| 0 <= k < i as int ==> a[k] == b[k],
                0 <= temp_sum <= 2*i as i32, // Reflect iteration impact within nested loop on temp_sum.
                a[( i ) as int] >= b[( i ) as int], // Ensure each step maintains or reduces a[i].
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        temp_sum = temp_sum + a[i]; // Accumulate temporary partial sum.
        sum = temp_sum; // Align sum with the current state of the temporary partial sum.
        i = i + 1;
    }  
    sum
}
}


// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1