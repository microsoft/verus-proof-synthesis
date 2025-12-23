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
	// First loop: setting a to 1
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
		a.len() == N,
		forall |j: int| 0 <= j < i as int ==> a[j] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	// Second loop: summing elements of a
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
		sum.len() == 1,
		a.len() == N,
		sum[0] <= i as i32,
		forall |j: int| 0 <= j < N ==> a[j] == 1,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	// Third loop: setting b to 1
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
		b.len() == N,
		forall |j: int| 0 <= j < i as int ==> b[j] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	// Fourth loop: summing elements of b
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
		sum.len() == 1,
		b.len() == N,
		sum[0] <= 2 * N,
		forall |j: int| 0 <= j < N ==> b[j] == 1,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	// Fifth loop: setting c to 1
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
		c.len() == N,
		forall |j: int| 0 <= j < i as int ==> c[j] == 1,
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	// Sixth loop: summing elements of c
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
		sum.len() == 1,
		c.len() == N,
		sum[0] <= 3 * N,
		forall |j: int| 0 <= j < N ==> c[j] == 1,
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}
// Score: (5, 4)
// Safe: True