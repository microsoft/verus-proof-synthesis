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
			i <= N as usize,
			N > 0,
			a.len() == N,
			N < 1000,
			sum.len() == 1,
			forall |k: int| 0 <= k < i as int ==> a[k as int] == 1,
			forall |k: int| i as int <= k < N ==> a[k as int] == old(a)[k as int],
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			b.len() == N,
			N < 1000,
			sum.len() == 1,
			forall |k: int| 0 <= k < i as int ==> b[k as int] == 1,
			forall |k: int| i as int <= k < N ==> b[k as int] == old(b)[k as int],
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			c.len() == N,
			N < 1000,
			sum.len() == 1,
			forall |k: int| 0 <= k < i as int ==> c[k as int] == 1,
			forall |k: int| i as int <= k < N ==> c[k as int] == old(c)[k as int],
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			a.len() == N,
			sum.len() == 1,
			sum[0] <= i as i32,
			forall |k: int| k < i as int ==> a[k as int] == 1,
			exists |total: i32| total == i as i32 && sum[0] == total,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			b.len() == N,
			sum.len() == 1,
			sum[0] <= N + (i as i32),
			forall |k: int| k < i as int ==> b[k as usize] == 1,
			exists |total: i32| total == i as i32 + N && sum[0] == total,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			c.len() == N,
			sum.len() == 1,
			sum[0] <= 2 * N + (i as i32),
			forall |k: int| k < i as int ==> c[k as usize] == 1,
			exists |total: i32| total == i as i32 + 2 * N && sum[0] == total,
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}










// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2