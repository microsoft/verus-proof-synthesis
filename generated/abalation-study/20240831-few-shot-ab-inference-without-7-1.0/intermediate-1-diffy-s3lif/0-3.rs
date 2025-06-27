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
			i <= N as usize,
			a.len() == N,
			(0 <= i < a.len() ==> a@.subrange(0, i as int).forall(|v| v == 1)),
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			(0 <= i <= N as usize ==> 
				forall |j: int| 0 <= j < i ==> a[j] == 4),
			forall |k: int| 0 <= k < N ==> a[k] == 1 || a[k] == 4,
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
			i <= N as usize,
			sum.len() == 1,
			a.len() == N,
			sum[0] <= 4 * i as i32,
			forall |j:int| 0<= j < i ==> sum[0] == 4 * j,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1