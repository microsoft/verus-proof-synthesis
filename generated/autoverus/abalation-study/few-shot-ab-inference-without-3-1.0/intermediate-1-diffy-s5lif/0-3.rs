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
		sum[0] == 6 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			old(a).len() == N,
			N > 0,
			N < 1000,
			forall |k: int| 0 <= k < i as int ==> a[k as int] == 1,
			forall |k: int| i as int <= k < N as int ==> a[k as int] == old(a)[k as int],
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			old(a).len() == N,
			N > 0,
			N < 1000,
			forall |k: int| 0 <= k < i as int ==> a[k as int] == 6,
			forall |k: int| i as int <= k < N as int ==> a[k as int] == 1,
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 5);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			sum.len() == 1,
			N > 0,
			N < 1000,
			forall |k: int| 0 <= k < sum.len() as int ==> old(sum)[k as int] == 0,
			sum[0] == 6 * i as i32,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}






// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 4