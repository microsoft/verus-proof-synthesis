
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 4 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			a.len() == N as usize,
			sum.len() == 1,
			old(a).len() == N, 
			old(sum).len() == 1,
			sum[0] == 4 * (i as i32), // to support the post-condition 
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			a.len() == N as usize,
			sum.len() == 1,
			old(a).len() == N, 
			old(sum).len() == 1,
			sum[0] == 4 * N, // to support the post-condition 
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 3);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			a.len() == N as usize,
			sum.len() == 1,
			old(a).len() == N, 
			old(sum).len() == 1,
			sum[0] == 4 * N, // to support the post-condition 
			forall |j:int| 0 <= j < i ==> a[j] != 1, // to support the loop logic 
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5