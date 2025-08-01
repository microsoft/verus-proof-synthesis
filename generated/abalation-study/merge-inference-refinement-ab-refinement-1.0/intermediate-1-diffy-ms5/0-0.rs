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
		sum[0] <= 4 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N,
			a.len() == N,
			0 < N < 1000,
			forall |k:int| 0 <= k < i ==> a[k] == (k % 5) as i32,
	{
		a.set(i, (i % 5) as i32);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			a.len() == N,
			sum.len() == 1,
			0 < N < 1000,
			sum[0] <= 4 * N,
			// Invariant for sum being correct for all increments up to current i
			if (i > 0) ==> sum[0] == (i - 1).fold(0, |acc, idx| acc + a[idx]),
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