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
		invariant
			i <= N as usize,
			a.len() == N,
			N > 0,
			N < 1000,
			forall |k:usize| k < i ==> a[( k ) as int] == (k % 3) as i32,
	{
		a.set(i, (i % 3) as i32);
		i = i + 1;
	}

	i = 0;
	let mut tmp_sum: i32 = 0;

	while (i < N as usize)
		invariant
			i <= N as usize,
			0 <= tmp_sum <= 2 * i as i32,
	{
		if (i == 0) {
			sum.set(0, 0);
			tmp_sum = 0;
		} else {
			sum.set(0, sum[0] + a[i]);
			tmp_sum += a[i];
		}
		i = i + 1;
	}
	assert!(tmp_sum <= 2 * N); // Ensure that the sum[0] follows the guarantee
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1