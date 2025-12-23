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
		sum[0] <= 2 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			b.len() == N,
			sum.len() == 1,
			N > 0,
			N < 1000,
			forall |k: int| 0 <= k < i as int ==> a[k as int] == 1,
			forall |k: int| i as int <= k < N as int ==> old(a)[k] == a[k as int],
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			b.len() == N,
			sum.len() == 1,
			N > 0,
			N < 1000,
			forall |k: int| 0 <= k < i as int ==> b[k as int] == 1,
			forall |k: int| i as int <= k < N as int ==> old(b)[k] == b[k as int],
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			b.len() == N,
			sum.len() == 1,
			N > 0,
			N < 1000,
			sum[0] <= i as i32,
			forall |k: int| 0 <= k < N as int ==> a[k as int] == 1,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			b.len() == N,
			sum.len() == 1,
			N > 0,
			N < 1000,
			sum[0] <= N + i as i32,
			forall |k: int| 0 <= k < N as int ==> a[k as int] == 1,
			forall |k: int| 0 <= k < N as int ==> b[k as int] == 1,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}
}
}







// Score: (5, 0)
// Safe: True