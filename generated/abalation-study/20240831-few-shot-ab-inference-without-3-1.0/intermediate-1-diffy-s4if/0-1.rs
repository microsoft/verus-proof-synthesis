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
			N > 0,
			i <= N as usize,
			a.len() == N,
			N < 1000,
			forall |k: int| 0 <= k < i ==> a[k] == 4,
	{
		a.set(i, 4);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			N > 0,
			i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			sum[0] <= 4 * i as i32, 
			N < 1000,
			forall |k: int| 0 <= k < N ==>
				(a[k] == 4 && sum[0] == 4 * (k + 1) ||
				(a[k] != 4)),
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
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5