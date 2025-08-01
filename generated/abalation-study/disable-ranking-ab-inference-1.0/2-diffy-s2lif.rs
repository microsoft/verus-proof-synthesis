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
		sum[0] == 3 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
            0 < N < 1000,
			a.len() == N,
			forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
            0 < N < 1000,
			a.len() == N,
			forall |k: usize| 0 <= k < i ==> a[( k ) as int] == 3,
			forall |k: usize| i <= k < N ==> a[( k ) as int] == 1,
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 2);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
            0 < N < 1000,
			a.len() == N,
			sum.len() == 1,
			forall |k: usize| 0 <= k < N ==> a[( k ) as int] == 3,
			sum[0] == i as i32 * 3,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}




// Score: (4, 0)
// Safe: True