
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
	ensures
		sum[0] == 0,
{
	let mut i: usize = 0;
	while (i < N as usize)
	invariant
		i <= N,
		N > 0,
		a.len() == N,
		sum.len() == 1,
	{
		a.set(i, i % 1 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
	invariant
		i <= N,
		N > 0,
		a.len() == N,
		sum.len() == 1,
		sum[0] <= i * (N - 1), // Added by AI, upper bound for sum[0]
		forall |k: int| 0 <= k < a.len() ==> a[k] == old(a)[k],
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


// 			sum.set(0, sum[0] + a[i]);
//   None: sum[0] + a[i]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True