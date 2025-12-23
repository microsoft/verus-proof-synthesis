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
		sum[0] == 3 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while i < N as usize
		invariant
			0 <= i as int <= N,
			a@.len() == N,
			sum@.len() == 1,
			forall |j: int| 0 <= j < i as int ==> a[j] == 3,
			sum[0] == 0
	{
		a.set(i, 3);
		i = i + 1;
	}

	i = 0;

	while i < N as usize
		invariant
			0 <= i as int <= N,
			a@.len() == N,
			sum@.len() == 1,
			forall |j: int| 0 <= j < N ==> a[j] == 3,
			sum[0] == 3 * i as int
	{
		if a[i] == 3 {
			sum.set(0, sum[0] + a[i]);
		} else {
			sum.set(0, sum[0] * a[i]);
		}
		i = i + 1;
	}
}
}
// Score: (2, 2)
// Safe: False