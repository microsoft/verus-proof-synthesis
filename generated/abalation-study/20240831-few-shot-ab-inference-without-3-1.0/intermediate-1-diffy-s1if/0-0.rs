use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		sum[0] == N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			N > 0,
			i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |k: int| 0 <= k < i as int ==> a[k] == 1,
			forall |k: int| i as int <= k < N ==> a[k] == old(a)[k], //elements not written yet retain original values
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			N > 0,
			i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |k: int| 0 <= k < i as int ==> a[k] == 1,
			sum[0] == forall |k: int| 0 <= k < i as int ==> ( 1 * k ) as bool, // sum(i-1) stores the count of '1' in the sequence up to i
	{
		if (a[i] == 1) {
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