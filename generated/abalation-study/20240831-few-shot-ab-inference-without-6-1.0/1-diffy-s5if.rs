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
		sum[0] == 5 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			0 <= i <= N,
			N < 1000,
			a.len() == N,
			sum.len() == 1,
			forall |k:int| 0 <= k < i ==> a[k as int] == 5,
	{
		a.set(i, 5);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			N < 1000,
			a.len() == N,
			sum.len() == 1,
			forall |k:int| 0 <= k < N ==> a[k as int] == 5,
			sum[0] == 5 * i, // to support function post-condition
	{
		if (a[i] == 5) {
			sum.set(0, sum[0] + a[i]);
		} else {
			sum.set(0, sum[0] * a[i]);
		}
		i = i + 1;
	}
}
}


// Score: (3, 0)
// Safe: True