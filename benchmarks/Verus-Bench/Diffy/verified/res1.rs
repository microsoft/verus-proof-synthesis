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
			a.len() == N,
			forall |k:int| 0 <= k < i ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			b.len() == N,
			forall |k:int| 0 <= k < i ==> b[k] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum.len() == 1,
			sum[0] == i,
            a.len() == N,
			forall |k:int| 0 <= k < N ==> a[k] == 1,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum.len() == 1,
            b.len() == N,
			sum[0] == N + i,
            N < 1000,
			forall |k:int| 0 <= k < N ==> b[k] == 1,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}
}
}




