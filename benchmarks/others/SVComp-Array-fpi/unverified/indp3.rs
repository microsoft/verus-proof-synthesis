use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == k * k,
{
	let mut i: usize = 0;

	while (i < N as usize)
	{
		a.set(i, (i as i32 - 1) * (i as i32 - 1));
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	{
		a.set(i, a[i] + i as i32);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	{
		a.set(i, a[i] + i as i32);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	{
		a.set(i, a[i] - 1);
		i = i + 1;
	}
}
}