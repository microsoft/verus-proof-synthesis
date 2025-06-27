
use vstd::prelude::*;
fn main() {}
verus!{

    #[verifier::loop_isolation(false)]

    pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
    	requires 
    		old(a).len() == N,
    		old(sum).len() == 1,
    		N > 0,
    	ensures
    		sum[0] <= N,
    {
        let mut i: usize = 0;

        while (i < N as usize)
            invariant
                i <= N,
                0 < N,
                a.len() == N,
            {
                a.set(i, i % 2 );
                i = i + 1;
            }

        i = 0;
        
        while (i < N as usize)
            invariant
                i <= N,
                0 < N,
                sum.len() == 1,
                old(sum).len() == 1,
                old(a).len() == N,
                sum[0] <= N,
                forall |j:int| 0 <= j < i ==> a[j] % 2 == j % 2,
            {
                if (i == 0) {
                    sum.set(0, 0);
                } else {
                    sum.set(0, sum[0] + a[i]);
                }
                i = i + 1;
            }
    }
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5