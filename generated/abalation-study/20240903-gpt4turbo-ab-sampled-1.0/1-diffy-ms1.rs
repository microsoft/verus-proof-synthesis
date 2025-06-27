use vstd::prelude::*;
fn main() {}
verus!{

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
	        a.len() == N,
	        forall |k:int| 0 <= k < i ==> a[k] == 0, // since i % 1 == 0 for all i
	{
		a.set(i, i % 1 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
	    invariant
	        i <= N,
	        sum.len() == 1,
	        sum[0] == if i == 0 { old(sum)[0] } else { 0 },
	        a.len() == N,
	        forall |k:int| 0 <= k < N ==> a[k] == 0,
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
// Score: (3, 0)
// Safe: True