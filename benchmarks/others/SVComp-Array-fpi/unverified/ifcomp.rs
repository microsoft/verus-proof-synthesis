use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> c[k] == k * k * k,
{
	let mut i: usize = 0;

	while (i < N as usize)
	{
		if (i == 0) {
			a.set(0, 6);
		} else {
			a.set(i, a[i-1] + 6);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	{
		if (i == 0) {
			b.set(0, 1);
		} else {
			b.set(i, b[i-1] + a[i-1]);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	{
		if (i == 0) {
			c.set(0, 0);
		} else {
			c.set(i, c[i-1] + b[i-1]);
		}
		i = i + 1;
	}
}
}