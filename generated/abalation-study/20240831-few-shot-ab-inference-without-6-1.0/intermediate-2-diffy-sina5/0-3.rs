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
			0 <= i <= N,
			a.len() == N,
			b.len() == N,
			sum.len() == 1,
			N > 0, N < 1000,
			forall |j:int| 0 <= j < i ==> a[j] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			a.len() == N,
			b.len() == N,
			sum.len() == 1,
			N > 0, N < 1000,
			forall |j:int| 0 <= j < i ==> b[j] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			a.len() == N,
			b.len() == N,
			sum.len() == 1,
			sum[0] <= N * (i as i32),
			N > 0, N < 1000,
			forall |j:int| 0 <= j < N ==> a[j] == 1,
			forall |j:int| 0 <= j < N ==> b[j] == 1,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			a.len() == N,
			b.len() == N,
			sum.len() == 1,
			sum[0] <= 2 * N * (i as i32),
			N > 0, N < 1000,
			forall |j:int| 0 <= j < N ==> a[j] == 1,
			forall |j:int| 0 <= j < N ==> b[j] == 1,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			a.len() == N,
			b.len() == N,
			sum.len() == 1,
			sum[0] == 2 * N,
			N > 0, N < 1000,
			forall |j:int| 0 <= j < i ==> a[j] == 2 * N + 1,
			forall |j:int| i <= j < N ==> a[j] == 1,
			forall |j:int| 0 <= j < N ==> b[j] == 1,
	{
		a.set(i, a[i] + sum[0]);
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 3, Errors: 3, Verus Errors: 6