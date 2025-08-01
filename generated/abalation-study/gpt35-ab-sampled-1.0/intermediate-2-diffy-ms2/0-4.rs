
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
            sum[0] <= N,
        {
		a.set(i, i % 2 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
        invariant
            i <= N,
            sum.len() == 1,
            N > 0,
            old(a).len() == N,
            forall |j:int| 0 <= j < i ==> a[j] == j % 2, // Invariant for array a
            sum[0] <= N, // Invariant for array sum
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
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5