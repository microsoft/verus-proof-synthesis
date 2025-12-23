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
		sum[0] == 5 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |k:int| 0 <= k < i ==> a[k] == 5,
	{
		a.set(i, 5);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |k:int| 0 <= k < i ==> if a[k] == 5 { sum[0] == 5 * k as i32 } else { true }, //to dynamically verify sum[0] changes as expected
	{
		if (a[i] == 5) {
			sum.set(0, sum[0] + a[i]);
		} else {
			sum.set(0, sum[0] * a[i]);
		}
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4