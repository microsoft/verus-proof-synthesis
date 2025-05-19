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
		sum[0] == 2 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |k:int| 0<= k < i ==> a[k] == 1,
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
			forall |k:int| 0<= k < i ==> a[k] == 2,
			forall |k:int| i<= k < N ==> a[k] == 1,
			a.len() == N,
		decreases
			N - i,
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 1);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == 2,
			sum[0] == 2 * i,
			sum.len() == 1,
			a.len() == N,
			N < 1000,
		decreases
			N - i,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}