

use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
.requires 
	old(a).len() == N,
	old(sum).len() == 1,
	N > 0,
.ensures
	sum[0] <= N,
{
	let mut i: usize = 0;
	while (i < N)
		invariant
			i <= N,
			a.len() == N,
			forall |k:int| 0 <= k < (i as int) ==> a[k as usize] == k % 2,
	{
		a.set(i, i % 2 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N)
		invariant
			i <= N,
			sum[0] <= i,
			forall |k:int| 0 <= k < N ==> a[k] == k % 2,
			forall |k:int| 0 <= k < (i as int) ==> sum[0] == (0..(i as int)).map(|x| a[x as usize] ).sum(),
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