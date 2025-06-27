

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
			a.len() == N,
			sum.len() == 1,
			forall |j: usize| 0 <= j < i ==> a[j] == (j % 2),
			forall |j: usize| i <= j < N ==> a[j] == old(a)[j],
	{
		a.set(i, i % 2 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N)
		invariant
			i <= N,
			a.len() == N,
			sum.len() == 1,
			forall |j: usize| 0 <= j <= i ==> if j == 0 then sum[j] == 0 else sum[j] == sum[j-1] + a[j],
			sum[0] <= i,
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