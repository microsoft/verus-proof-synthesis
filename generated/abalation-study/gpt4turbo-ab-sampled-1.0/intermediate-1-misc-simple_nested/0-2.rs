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
            i <= N,
            N <= 0x3FFF_FFFF,
            a.len() == N,
            b.len() == N,
            0 <= sum <= 2*i,
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                j <= i,
                a[( i ) as int] == b[( i ) as int] + 1 - j as i32,
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        // Ensuring after the nested loop a[i] is restored to b[i] + 1
        assert(a[( i ) as int] == b[( i ) as int] + 1); // This assertion is integral to the logic of the function and helps illustrate the state after the nested loop execution.
        sum = sum + a[i];
        i = i + 1;
    }  
    sum
}
}




// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 10