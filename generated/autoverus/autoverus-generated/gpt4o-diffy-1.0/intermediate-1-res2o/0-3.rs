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
			i <= N,
			a.len() == N,
			N > 0,
			N < 1000,
			forall |j: int| 0 <= j < i ==> a[j] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			b.len() == N,
			N > 0,
			N < 1000,
			forall |j: int| 0 <= j < i ==> b[j] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			c.len() == N,
			N > 0,
			N < 1000,
			forall |j: int| 0 <= j < i ==> c[j] == 1,
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			N > 0,
			N < 1000,
			sum.len() == 1,
			forall |j: int| 0 <= j < i ==> a[j] == 1,
			sum[0] <= i,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			N > 0,
			N < 1000,
			sum.len() == 1,
			forall |j: int| 0 <= j < i ==> b[j] == 1,
			sum[0] <= N + i,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			N > 0,
			N < 1000,
			sum.len() == 1,
			forall |j: int| 0 <= j < i ==> c[j] == 1,
			sum[0] <= 2 * N + i,
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 4, Errors: 3, Verus Errors: 12