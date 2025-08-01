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
		sum[0] == 2 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;

	while i < N as usize
	invariant
		0 <= i <= N as usize,
		a@.len() == N as int,
		sum@.len() == 1,
		forall |k:int| 0 <= k < i as int ==> a[k] == 1
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while i < N as usize
	invariant
		0 <= i <= N as usize,
		a@.len() == N as int,
		sum@.len() == 1,
		forall |k:int| 0 <= k < i as int ==> a[k] == 2,
		forall |k:int| i <= k < N as int ==> a[k] == 1
	{
		if a[i] == 1 {
			a.set(i, a[i] + 1);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while i < N as usize
	invariant
		0 <= i <= N as usize,
		a@.len() == N as int,
		sum@.len() == 1,
		sum[0] == 2 * i as int,
		forall |k:int| 0 <= k < i as int ==> a[k] == 2,
		forall |k:int| i <= k < N as int ==> a[k] == 2
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}
// Score: (3, 2)
// Safe: False