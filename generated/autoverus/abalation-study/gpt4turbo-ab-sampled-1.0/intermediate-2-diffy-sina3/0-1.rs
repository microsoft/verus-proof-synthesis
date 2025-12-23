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
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			b.len() == N,
			sum.len() == 1,
			N > 0,
			N < 1000,
			forall |k:int| 0 <= k < i ==> a[k] == 1,
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
			forall |k:int| 0 <= k < i ==> b[k] == 1,
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
			sum[0] == i as i32,
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
            sum[0] == N as i32,
			forall |k:int| 0 <= k < i ==> a[k] == N + 1,
	{
		a.set(i, b[i] + sum[0]);
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 4