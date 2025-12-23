
use vstd::prelude::*;
fn main() {}
verus! {
proof fn lemma_sum_lower_bound(b: Seq<i32>, i: int, j: int)
    requires
        0<= i <= j < b.len(),
        forall |k:int| i <= k < j ==> k+1 <= b[k],
    ensures
        i+1 <= b[i],
    {
        assert(i+1 <= b[i]);
    }

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
            N <= sum <= 2*N,
            i <= N as usize,
            b.len() == N as usize,
            a.len() == N as usize,
            forall |k:int| k <= #[trigger] b[k] <= k + 1,
            forall |k:int| 0 <= k < i ==> i+1 <= b[k],
    {  
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= j <= i,
                forall |k:int| 0 <= k < j ==> j+1 <= b[k], // to support the post-condition
        {
            a.set(i, a[i] - 1);
            j = j + 1;

            proof {
                lemma_sum_lower_bound(b@, i as int, j as int);
            }
        }
        sum = sum + a[i];
        i = i + 1;
    }  
    sum
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 4, Verus Errors: 12