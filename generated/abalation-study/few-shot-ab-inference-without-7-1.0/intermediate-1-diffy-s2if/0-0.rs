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
			0 <= i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |j: int| 0 <= j < i ==> a[j as int] == 2,
	{
		a.set(i, 2);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |j: int| 0 <= j < N ==> a[j as int] == 2,
			sum[0] == i as i32 * 2,
	{
		if (a[i] == 2) {
			sum.set(0, sum[0] + a[i]);
		} else {
			sum.set(0, sum[0] * a[i]);
		}
		i = i + 1;
	}
}
}


// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2