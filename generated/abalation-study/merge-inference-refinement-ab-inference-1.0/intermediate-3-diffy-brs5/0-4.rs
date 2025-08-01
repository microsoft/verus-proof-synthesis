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
		sum[0] <= 5 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
	    invariant
	        i <= N as usize,
	        a.len() == N,
	        forall |k:int| 0 <= k < N ==> a[k] == old(a)[k],
	        forall |k:int| 0 <= k < i ==> (if k % 5 == 0 { a[k] == 5 } else { a[k] == 0 }),
	        N > 0,
        	N < 1000,
	{
		if (i % 5 == 0) {
			a.set(i, 5);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
	    invariant
	        i <= N as usize,
	        sum.len() == 1,
	        a.len() == N,
	        N > 0,
        	N < 1000,
	        forall |k:int| 0 <= k < N ==> a[k] == old(a)[k],
	        forall |k:int| 0 <= k < N ==>(if k % 5 == 0 { a[k] == 5 } else { a[k] == 0 }),
	        sum[0] <= if i == 0 { 0 } else { 5 * i as i32 / 5 },
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
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3