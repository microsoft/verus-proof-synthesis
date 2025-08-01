

use vstd::prelude::*;
fn main() {}

verus!{

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
	ensures
		sum[0] <= N,
{
	let mut i: usize = 0;

    // First loop to initialize a
	while (i < N as usize)
	    invariant 
	        i <= N,
	        a.len() == N,
	        sum.len() == 1,
	        // Ensure a is properly initialized up to i
	        forall |k: int| 0 <= k < i as int ==> a[k] == k % 2,
    {
		a.set(i, i % 2 );
		i = i + 1;
	}

	i = 0;
    
    // Second loop to compute the sum of a
	while (i < N as usize)
	    invariant 
	        i <= N,
	        a.len() == N,
	        sum.len() == 1,
	        // Ensure the sum is correctly accumulating up to i
	        sum[0] == s!(0..i-1 as i32: j => a[j] % 2)
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1