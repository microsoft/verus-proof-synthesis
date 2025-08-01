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
			0 <= N < 1000,
			i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |k: int| 0 <= k < i ==> a[k as int] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= N < 1000,
			i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |k: int| 0 <= k < N ==> (k < i ==> a[k as int] == 6) && (k >= i ==> a[k as int] == 1),
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
			0 <= N < 1000,
			i <= N as usize,
			sum.len() == 1,
			forall |k: int| 0 <= k < N ==> a[k as int] == 6,
			sum[0] == 6 * (i as i32), //to support function post-condition
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}




// is safe: True
// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1