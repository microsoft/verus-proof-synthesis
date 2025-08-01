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
		forall |k:int| 0 <= k < N ==> a[k] == 2 * N + 1,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			N > 0,
			N < 1000,
			a.len() == N,
			old(a).len() == N,
			forall |k:int| 0 <= k < i as int ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			N > 0,
			N < 1000,
			b.len() == N,
			old(b).len() == N,
			forall |k:int| 0 <= k < i as int ==> b[k] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			N > 0,
			N < 1000,
			sum.len() == 1,
			a.len() == N,
			forall |k:int| 0 <= k < sum.len() ==> sum[k] >= 0,
			forall |k:int| 0 <= k < i as int ==> sum[0] >= 0,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			N > 0,
			N < 1000,
			sum.len() == 1,
			b.len() == N,
			forall |k:int| 0 <= k < sum.len() ==> sum[k] >= 0,
			forall |k:int| 0 <= k < i as int ==> sum[0] >= 0,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			N > 0,
			N < 1000,
			sum.len() == 1,
			a.len() == N,
			forall |k:int| 0 <= k < i as int ==> a[k] == 2 * N + 1,
			forall |k:int| i <= k < N as int ==> a[k] >= 1,
			sum[0] == 2 * N,
	{
		a.set(i, a[i] + sum[0]);
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1