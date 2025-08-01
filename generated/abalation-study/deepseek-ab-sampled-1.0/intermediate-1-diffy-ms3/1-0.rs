

use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 2 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant 
			i <= N,
			a.len() == N,
			forall |k : int| 0 <= k < i ==> a[k] == (k % 3),
	{
		a.set(i, (i % 3) as i32);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant 
			i <= N,
			sum.len() == 1,
			sum[0] == seq::sum(a@.subrange(1, i as int)),
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;
	}

	proof {
		let a_sum: i32 = sum[0];
		let a_seq: Seq<i32> = a@;
		let n: i32 = N;

		forall |k : int| 1 <= k < n as int ==> a_seq[k] <= 2;
		a_sum <= seq::sum(a_seq.subrange(1, n as int).map(|x| 2));
		a_sum <= 2 * n as i32;
	}
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2