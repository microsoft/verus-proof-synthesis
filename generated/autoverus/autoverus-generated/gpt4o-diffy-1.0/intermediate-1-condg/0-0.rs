use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == 0,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant 
			N > 0,
			i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |k:int| 0 <= k < i as int ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			sum.len() == 1,
			a.len() == N,
			N > 0,
			forall |k:int| 0 <= k < i as int ==> sum[0] == k,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			sum.len() == 1,
			a.len() == N,
			forall |k:int| 0 <= k < i as int ==> a[k] == 0,
			sum[0] == N, // sum should be equal to N, implies that each element in `a` will be 1.
	{
		if (sum[0] == N) {
			a.set(i, a[i] - 1);
		} else {
			a.set(i, a[i] + 1);
		}
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1