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
	sum.set(0, 0);
	let mut i: usize = 0;

	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			a.len() == N,
			old(a).len() == N,
			N < 1000,
			forall |k: int| 0 <= k < i ==> a[k as int] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			sum.len() == 1,
			a.len() == N,
			sum[0] >= 0,
			old(sum).len() == 1,
			old(a).len() == N,
			sum[0] <= i as i32,
			N < 1000,
			forall |k: int| 0 <= k < N ==> a[k as int] == 1,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			b.len() == N,
			old(b).len() == N,
			N < 1000,
			forall |k: int| 0 <= k < i ==> b[k as int] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			sum.len() == 1,
			b.len() == N,
			sum[0] >= 0,
			old(sum).len() == 1,
			old(b).len() == N,
			sum[0] <= 2 * N,
			sum[0] <= i as i32 + N,
			N < 1000,
			forall |k: int| 0 <= k < N ==> b[k as int] == 1,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			c.len() == N,
			old(c).len() == N,
			N < 1000,
			forall |k: int| 0 <= k < i ==> c[k as int] == 1,
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			sum.len() == 1,
			c.len() == N,
			sum[0] >= 0,
			old(sum).len() == 1,
			old(c).len() == N,
			sum[0] <= 3 * N,
			sum[0] <= (2 * N) as i32 + i as i32,
			N < 1000,
			forall |k: int| 0 <= k < N ==> c[k as int] == 1,
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}






// Score: (7, 0)
// Safe: True