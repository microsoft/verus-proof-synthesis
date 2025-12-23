use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
	ensures
		sum[0] <= N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N,
			a.len() == N,
			sum.len() == 1,
			// Invariant for a: for filling even indices with 0, odd with 1 in first round
			forall |k: int| 0 <= k < i ==> a[k] == k % 2,
	{
		a.set(i, i % 2 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			i <= N,
			a.len() == N,
			sum.len() == 1,
			// Invariant to ensure sum is correctly computed
			forall |k: int| 0 <= k < N ==> a[k] == k % 2,
			// Invariant that the sum does not exceed N
			sum[0] <= N,
			// Sum computation invariant (handles first iteration specially)
			(
				i == 0 ==> sum[0] == 0
			) &&
			(
				i > 0 ==> sum[0] == (seq!(|k: int| 0 <= k < i => if k % 2 == 0 {0} else {1}).sum() as usize)
			),
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