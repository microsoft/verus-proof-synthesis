
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
			N < 1000,
			a.len() == N,
			sum.len() == 1,
			forall |j:int| 0 <= j < i ==> a[j] == 1,
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
			forall |j:int| 0 <= j < N ==> a[j] == 1,
			forall |j:int| 0 <= j < i ==> (a[j] == 4) || (a[j] == 0),
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 3);
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
			sum[0] == 4 * i as i32 + fold(a.subrange(0, i as int), 0, |acc, x| acc + x),
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1