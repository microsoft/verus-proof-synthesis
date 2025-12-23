
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == N + 1,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N as int,
			b.len() == N as int,
			sum.len() == 1,
			N > 0,
			forall |k:int| 0 <= k < i ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N as int,
			b.len() == N as int,
			sum.len() == 1,
			N > 0,
			forall |k:int| 0 <= k < N ==> a[k] == 1, // to support function post-condition
			forall |k:int| 0 <= k < i ==> b[k] == 1,     // this loop is unnecessary but added for illustrative purposes
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N as int,
			b.len() == N as int,
			sum.len() == 1,
			N > 0,
			forall |k:int| 0 <= k < N ==> a[k] == 1,
			forall |k:int| 0 <= k < N ==> b[k] == 1,
			sum[0] == i,	// sum[0] contains the sum of all 1s encountered so far
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N as int,
			b.len() == N as int,
			sum.len() == 1,
			N > 0,
			forall |k:int| 0 <= k < N ==> a[k] == 1,
			forall |k:int| 0 <= k < N ==> b[k] == 1,
			sum[0] == N,	//sum[0] has the total sum of all 1s
			forall |k:int| 0 <= k < i ==> a[k] == b[k] + sum[0], //this loop is unnecessary but added to support the post-condition of the function
	{
		a.set(i, b[i] + sum[0]);
		i = i + 1;
	}
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 4, Errors: 1, Verus Errors: 3