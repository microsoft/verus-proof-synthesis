

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
    proof {
        reveal(Seq::len);
    }
    while (i < N as usize) 
        invariant 
            i <= N,
            sum == old(a).len(),
            a.len() == N as usize,
            b.len() == N as usize,
            forall |k:usize| k <i ==> N <= 1 <= 2,
            old(a).len() as i32 <= 2*N,
    {  
        a.set(i, b[i as usize] + 1);
        let mut j: usize = 0;
        proof {
            reveal(Seq::len);
        }
        while (j < i)
            invariant 
                j <= i,
                i <= N as usize,
                a.len() == N as usize,
                b.len() == N as usize,
                a[( i ) as int] == b[i as int] + 1 - j as i32,
        {
            a.set(i, a[i] - 1);
            proof {
                reveal(Seq::len);
            }
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