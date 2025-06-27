use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, N: i32, m: i32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] <= N,
{
	let mut i: usize = 0;

	while (i < N as usize)
		invariant
			i <= N,
			0 < N,
			a.len() == N,
			forall |k:int| 0 <= k < i ==> a[k] == m,
	{
		a.set(i, m);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			a.len() == N,
			0 < N,
			forall |k:int| 0 <= k < i ==> a[k] <= N,
			forall |k:int| i <= k < N ==> a[k] == m,
	{
		if (a[i] < N) {
			a.set(i, a[i]);
		} else {
			a.set(i, N);
		}
		i = i + 1;
	}
}
}
// Score: (3, 0)
// Safe: True