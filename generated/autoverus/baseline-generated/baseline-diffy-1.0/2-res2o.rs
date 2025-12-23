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

	// Invariant for initializing 'a'
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			a@.len() == N,
			forall |k: int| 0 <= k < i ==> a[k] == 1,
			forall |k: int| i <= k < N as int ==> old(a)[k] == a[k]
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;

	// Invariant for initializing 'b'
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			b@.len() == N,
			forall |k: int| 0 <= k < i ==> b[k] == 1,
			forall |k: int| i <= k < N as int ==> old(b)[k] == b[k]
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;

	// Invariant for initializing 'c'
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			c@.len() == N,
			forall |k: int| 0 <= k < i ==> c[k] == 1,
			forall |k: int| i <= k < N as int ==> old(c)[k] == c[k]
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;

	// Invariant for summing 'a'
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			sum@.len() == 1,
			sum[0] <= i,
			a@.len() == N,
			forall |k: int| 0 <= k < N as int ==> a[k] == 1
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;

	// Invariant for summing 'b'
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			sum@.len() == 1,
			sum[0] <= N + i,
			b@.len() == N,
			forall |k: int| 0 <= k < N as int ==> b[k] == 1
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;

	// Invariant for summing 'c'
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			sum@.len() == 1,
			sum[0] <= 2 * N + i,
			c@.len() == N,
			forall |k: int| 0 <= k < N as int ==> c[k] == 1
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}
// Score: (5, 2)
// Safe: True