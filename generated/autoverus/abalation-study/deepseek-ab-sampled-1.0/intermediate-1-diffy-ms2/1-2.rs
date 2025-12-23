

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

	while (i < N as usize)
		// Loop Invariant 1: `i` is within bounds
		invariant 
			i <= N,
			// Loop Invariant 2: `a` maintains its length `N`
			a.len() == N,
			// Loop Invariant 3: For all `k < i`, `a[k]` has been set to `k % 2`
			forall |k: usize| 0 <= k < i ==> a[( k ) as int] == k % 2,

	{
		a.set(i, i % 2 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		// Loop Invariant 1: `i` is within bounds
		invariant 
			i <= N,
			// Loop Invariant 2: `sum` maintains its length 1
			sum.len() == 1,
			// Loop Invariant 3: `sum[0]` contains the sum of `a[0]` to `a[i-1]`
			forall |k: usize| 0 <= k < i ==> sum[0] == sum(a[( 0..k ) as int]),
			// Loop Invariant 4: All elements `a[k]` for `k < i` are correct
			forall |k: usize| 0 <= k < i ==> a[k] == k % 2,

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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3