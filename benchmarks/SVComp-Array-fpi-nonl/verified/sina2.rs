use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			forall |k:int| 0 <= k < i ==> a[k] == 1,
			a.len() == N,
		decreases
			N - i,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0 <= k < N ==> a[k] == 1,
			sum[0] == i,
			a.len() == N,
			sum.len() == 1,
		decreases
			N - i,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			sum[0] == N,
			forall |k:int| 0 <= k < i ==> a[k] == N + 1,
			forall |k:int| i <= k < N ==> a[k] == 1,
			a.len() == N,
			sum.len() == 1,
			N < 1000,
		decreases
			N - i,
	{
		a.set(i, a[i] + sum[0]);
		i = i + 1;
	}
}
}