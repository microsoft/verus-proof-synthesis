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
			N > 0,
			N < 1000,
			a.len() == N,
			sum.len() == 1,
			i <= N as usize,
			forall |j: int| 0 <= j < i ==> a[j as int] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			N > 0,
			N < 1000,
			a.len() == N,
			sum.len() == 1,
			i <= N as usize,
			forall |j: int| 0 <= j < i ==> a[j as int] == 2,
			forall |j: int| i <= j < N as usize ==> a[j as int] == 1,
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
			N > 0,
			N < 1000,
			a.len() == N,
			sum.len() == 1,
			i <= N as usize,
			sum[0] <= 2 * i as i32,
			forall |j: int| 0 <= j < i ==> sum[0] == 2 * j + 2,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}



// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1