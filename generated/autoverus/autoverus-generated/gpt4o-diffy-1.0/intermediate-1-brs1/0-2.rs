use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		sum[0] <= N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			a.len() == N,
			sum.len() == 1,
			forall |k: int| 0 <= k < i ==> a[k] == 1 || a[k] == 0,
			forall |k: int| 0 <= k < i && k % 1 == 0 ==> a[k] == 1,
			forall |k: int| 0 <= k < i && k % 1 != 0 ==> a[k] == 0,
	{
		if (i % 1 == 0) {
			a.set(i, 1);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N,
			a.len() == N,
			sum.len() == 1,
			forall |k: int| 0 <= k < i ==> sum[0] <= k + 1, // Sum at most equals number of elements processed
			forall |k: int| k <= i < N && k % 1 == 0 ==> a[k] == 1,
			forall |k: int| k <= i < N && k % 1 != 0 ==> a[k] == 0,
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1