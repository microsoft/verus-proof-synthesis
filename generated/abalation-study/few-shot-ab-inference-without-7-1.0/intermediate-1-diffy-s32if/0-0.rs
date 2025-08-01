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
            sum.len() == 1,
            forall |j:usize| 0 <= j < i ==> a[j] == 1,
        invariant
            sum@.len() == 1 && sum@[0] == 0,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N)
        invariant
            i <= N,
            a.len() == N,
            forall |j:usize| 0 <= j < N ==> a[j] == 1 || a[j] == 4,
        invariant
            sum@.len() == 1 && sum@[0] == 0,
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
            a.len() == N,
            sum.len() == 1,
            forall |j:usize| 0 <= j < N ==> a[j] == 4,
            sum[0] <= 4 * i,
        invariant
            sum@.len() == 1 && sum@[0] <= 4 * i,
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
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1