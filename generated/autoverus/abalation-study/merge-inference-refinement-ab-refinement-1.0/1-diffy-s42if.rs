use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 5 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;

	while (i < N)
		invariant
			i <= N,
			a.len() == N,
			sum.len() == 1,
			N > 0,
			N < 1000,
			forall |k:int| 0 <= k < i ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			i <= N,
			a.len() == N,
			sum.len() == 1,
			N > 0,
			N < 1000,
			forall |k:int| 0 <= k < i ==> a[k] == 5,
			forall |k:int| i <= k < N ==> a[k] == 1,
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 4);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			i <= N,
			a.len() == N,
			sum.len() == 1,
			N > 0,
			N < 1000,
			forall |k:int| 0 <= k < N ==> a[k] == 5,
			sum[0] == 5 * i,
	{
		if (a[i] == 5)
		{
			sum.set(0, sum[0] + a[i]);
		} else {
			sum.set(0, sum[0] * a[i]);
		}
		i = i + 1;
	}
}
}
// Score: (4, 0)
// Safe: True