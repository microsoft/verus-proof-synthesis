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
	proof {
		assert(sum[0] <= i); // Added by AI
	}
	
	while (i < N as usize)
	invariant
		i <= N,
		N > 0,
		a.len() == N,
		sum.len() == 1,
		sum[0] <= i, // Added invariant to bound sum[0]
		a[( i ) as int] <= 1, // Added invariant to bound a[i]
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


// 		a[(i) as int] <= 1, // Added invariant to bound a[i]
//   None: a[(i) as int] <= 1

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: True