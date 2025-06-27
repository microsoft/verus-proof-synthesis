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
		sum[0] == 2 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;

	while (i < N)
		invariant 
			i <= N,
			a.len() == N,
			a.count(1) == i,
			sum.len() == 1,
			N < 1000,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant 
			i <= N,
			a.len() == N,
			a.count(2) == i,
			sum.len() == 1,
			N < 1000,
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 1);
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
			sum[0] == (a.take(i).count(2) as i32) * 2,
			N < 1000,
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3