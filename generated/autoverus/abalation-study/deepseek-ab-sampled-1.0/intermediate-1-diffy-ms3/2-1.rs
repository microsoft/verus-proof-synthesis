

use vstd::prelude::*;
fn main() {}

verus!{
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
	while (i < N as usize)
		// Invariants for the first loop
		invariant
			i <= N,
			a.len() == N,
			a.get(i).is_ok() --> a[i] <= 2,
			forall |j: int| 0 <= j < i --> 0 <= j as usize < a.len() && a[j as usize] <= 2,
	{
		a.set(i, (i % 3) as i32);
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		// Invariants for the second loop
		invariant
			i <= N,
			sum.len() == 1,
			sum[0] <= 2 * i,
			forall |j: int| 0 <= j <= i --> sum[0] >= j,
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