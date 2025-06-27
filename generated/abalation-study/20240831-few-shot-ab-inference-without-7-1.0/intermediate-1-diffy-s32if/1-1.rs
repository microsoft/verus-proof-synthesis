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
		sum[0] == 4 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N)
		invariant
			i <= N,
			a.len() == N,
			// a[..i] has been set to 1
			forall |j:int| 0 <= j < i ==> a[j as int] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			i <= N,
			a.len() == N,
			// a[..N] holds the correct transformation
			forall |j:int| 0 <= j < i ==> a[j as int] == 4,
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 3);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N)
		invariant
			i <= N,
			sum.len() == 1,
			a.len() == N,
			// sum contains 4 * number of processed elements in a
			sum[0] == 4 * (i as i32),
	{
		if (a[i] == 4) {
			sum.set(0, sum[0] + a[i]);
		} else {
			sum.set(0, sum[0] * a[i]);
		}
		i = i + 1;
	}
}
}


// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 5