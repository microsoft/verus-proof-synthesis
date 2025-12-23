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
		sum[0] == 4 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;

	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N as usize,
			forall |k:int| 0 <= k < i ==> a[k] == 4,
	{
		a.set(i, 4);
		i = i + 1;
	}

	i = 0;

	while (i < N as usize)
		invariant
			i <= N as usize,
			sum.len() == 1,
			forall |k:int| 0 <= k < i ==> sum[0] == 4 * k,
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1