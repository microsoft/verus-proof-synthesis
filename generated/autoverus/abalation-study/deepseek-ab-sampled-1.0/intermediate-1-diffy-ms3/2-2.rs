

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
		sum[0] <= 2 * N,
{
	let mut i: usize = 0;

	/* First Loop */
    while (i < N as usize)
        invariant 
            N < 1000,
            a.len() == N,
            sum.len() == 1,
            i <= N,
            forall |k: int| 0 <= k < i ==> a[k] == (k % 3),
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }

	/* Second Loop */
    i = 0; 
    while (i < N as usize)
        invariant 
            N < 1000,
            a.len() == N,
            sum.len() == 1,
            i <= N,
            sum[0] == sum_path(a, i), // Helper function to calculate sum of first i elements.
            sum[0] <= 2 * i,
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

/* Helper Function to Calculate Path Sum */
proof fn sum_path(a: &Vec<i32>, i: usize) -> i32 {
    let mut total: i32 = 0;
    for k in 0..i {
        total += a[k];
    }
    total
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1