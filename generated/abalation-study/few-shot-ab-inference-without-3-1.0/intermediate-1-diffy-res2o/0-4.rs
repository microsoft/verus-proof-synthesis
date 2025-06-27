use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] <= 3 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			0 <= N,
			N < 1000,
			a.len() == N,
			i <= N as usize,
			forall |k: int| 0 <= k < i ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= N,
			N < 1000,
			b.len() == N,
			i <= N as usize,
			forall |k: int| 0 <= k < i ==> b[k] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= N,
			N < 1000,
			c.len() == N,
			i <= N as usize,
			forall |k: int| 0 <= k < i ==> c[k] == 1,
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= N,
			N < 1000,
			sum.len() == 1,
			a.len() == N,
			i <= N as usize,
			sum[0] <= i,
			forall |k: int| 0 <= k < i ==> sum[0] == k as i32 + 1,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= N,
			N < 1000,
			sum.len() == 1,
			b.len() == N,
			i <= N as usize,
			sum[0] <= i + N,
			forall |k: int| 0 <= k < i ==> sum[0] == k as i32 + 1 + N,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= N,
			N < 1000,
			sum.len() == 1,
			c.len() == N,
			i <= N as usize,
			sum[0] <= 2 * N + i,
			forall |k: int| 0 <= k < i ==> sum[0] == k as i32 + 1 + 2 * N,
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1