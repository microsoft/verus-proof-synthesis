use vstd::prelude::*;
fn main() {}

verus! {
    pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 3 * N,
    {
        let mut i: usize = 0;

        // Initial loop to populate array a
        while i < N as usize
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            forall |j: int| 0 <= j < i as int ==> a[j] == (j % 4) as i32,
        {
            a.set(i, (i % 4) as i32);
            i = i + 1;
        }

        // Resetting i to 0
        i = 0;
        
        // Loop to calculate the cumulative sum
        while i < N as usize
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            sum@.len() == 1,
            forall |j: int| 0 <= j < N ==> a[j] == (j % 4) as i32,
            sum[0] <= 3 * i as i32,
        {
            if i == 0 {
                sum.set(0, 0);
            } else {
                sum.set(0, sum[0] + a[i]);
            }
            i = i + 1;
        }

        assert(sum[0] <= 3 * N);
    }
}
// Score: (1, 2)
// Safe: False