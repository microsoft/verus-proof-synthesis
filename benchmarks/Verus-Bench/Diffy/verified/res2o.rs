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
			forall |j: int| 0<= j < i ==> a[j] == 1,
			a.len() == N,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			forall |j: int| 0<= j < i ==> b[j] == 1,
			b.len() == N,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			forall |j: int| 0<= j < i ==> c[j] == 1,
			c.len() == N,
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum.len() == 1,
			sum[0] == i,
			forall |j: int| 0<= j < N ==> a[j] == 1,
			a.len() == N,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum.len() == 1,
			sum[0] == i + N,
			forall |j: int| 0<= j < N ==> b[j] == 1,
			b.len() == N,
			N < 1000,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum.len() == 1,
			sum[0] == i + 2 * N,
			forall |j: int| 0<= j < N ==> c[j] == 1,
			c.len() == N,
			N < 1000,
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}