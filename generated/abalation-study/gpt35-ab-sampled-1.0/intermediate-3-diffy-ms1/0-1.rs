
use vstd::prelude::*;
fn main() {}

verus!{
    pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
        requires 
            old(a).len() == N,
            old(sum).len() == 1,
            N > 0,
        ensures
            sum[0] == 0,
    {
        let mut i: usize = 0;
        // Loop Invariants:
        // a.len() == N, old(a).len() == N, sum.len() == 1, old(sum).len() == 1, N > 0, i <= N, 0 <= i
		while (i < N as usize)
            invariant
                a.len() == N, old(a).len() == N, sum.len() == 1, old(sum).len() == 1, N > 0, i <= N, 0 <= i,
            {
                a.set(i, i % 1 );
                i = i + 1;
            }

        i = 0;
        // Loop Invariants:
        // a.len() == N, old(a).len() == N, sum.len() == 1, old(sum).len() == 1, N > 0, i <= N, 0 <= i, forall |j:usize| 1 <= j <= i ==> sum[0] == a[0] + a[1] + ... + a[j-1]
        while (i < N as usize)
            invariant
                a.len() == N, old(a).len() == N, sum.len() == 1, old(sum).len() == 1, N > 0, i <= N, 0 <= i, forall |j:usize| 1 <= j <= i ==> sum[0] == a[0] + a[1] + ... + a[j-1],
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

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1