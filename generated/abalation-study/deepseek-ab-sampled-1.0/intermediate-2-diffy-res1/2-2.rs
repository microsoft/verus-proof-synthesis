

use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] <= 2 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum[0] == a[( ..i ) as int].len() as i32,
			a.len() == N,
		{
			sum.set(0, sum[0] + a[i]);
			i = i + 1;
		}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum[0] <= 2 * N,
			b.len() == N,
			a.len() == N,
			sum[0] <= 2 * (N),
		{
			sum.set(0, sum[0] + b[i]);
			i = i + 1;
		}
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2