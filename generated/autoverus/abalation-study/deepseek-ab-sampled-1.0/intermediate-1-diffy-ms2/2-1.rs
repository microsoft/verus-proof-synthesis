

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
	while (i < N)
		invariant
			i <= N,
			old(a).len() == N,
			forall |k: usize| 0 <= k < i ==>> a[k] == k % 2,
	{
		a.set(i, i % 2 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N)
		invariant
			i <= N,
			old(a).len() == N,
			sum.len() == 1,
			forall |k: usize| 0 <= k < i ==>> sum[0] == old(a).len() > 0 ? (sum[0] + a[k]) : 0,
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