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
			forall |k:int| 0 <= k < i ==> a[k] == 1,
			forall |k:int| i <= k < N ==> a[k] == old(a)[k],
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
			forall |k:int| 0 <= k < i ==> b[k] == 1,
			forall |k:int| i <= k < N ==> b[k] == old(b)[k],
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
			sum[0] == 0 || sum[0] == sum[0] + a[i-1], // Ensure sum is accurate up to the previous step
			forall |k:int| 0 <= k < i ==> sum[0] == k + 1, // Sum up to i includes all a[0] to a[i-1]
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
			forall |k:int| 0 <= k < i ==> sum[0] == 2 * i, // Ensure sum up to i includes both b[0] to b[i-1] and the previous sum
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
			forall |k:int| 0 <= k < i ==> a[k] == 2 * N + 1,
			forall |k:int| i <= k < N ==> a[k] == 1 + sum[0], // Ensure a[k] gets updated correctly
	{
		a.set(i, a[i] + sum[0]);
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1