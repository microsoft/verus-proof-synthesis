
use vstd::prelude::*;

verus! {
    pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
        requires 
            N > 0,
            N < 1000,
            old(a).len() == N,
            old(sum).len() == 1,
        ensures
            sum[0] <= 2 * N,
    {
        let mut i: usize = 0;

        while (i < N as usize)
            invariant
                i <= N as usize,
                a.len() == N,
                sum.len() == 1,
                forall |k| 0 <= k < i as int ==> a[k as usize] == (k as usize % 3) as i32,
        {
            a.set(i, (i % 3) as i32);
            i = i + 1;
        }

        i = 0;
        
        while (i < N as usize)
            invariant
                i <= N as usize,
                a.len() == N,
                sum.len() == 1,
                forall |k| 0 <= k < i as int ==> a[k as usize] == (k as usize % 3) as i32,
                sum[0] == (0..i as int - 1).sum(|k| a[k as usize]),
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5