
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
            sum[0] == 0,
    {
        let mut i: usize = 0;

        while (i < N as usize)
            invariant
                i <= N,
                a.len() == N,
                sum.len() == 1,
                N > 0,
                sum[0] == a.subrange(0, i).sum::<usize>(),
        {
            a.set(i, i % 1 );
            i = i + 1;
        }

        i = 0;
        
        while (i < N as usize)
            invariant
                i <= N,
                a.len() == N,
                sum.len() == 1,
                N > 0,
                sum[0] == a.subrange(0, i).sum::<usize>(),
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2