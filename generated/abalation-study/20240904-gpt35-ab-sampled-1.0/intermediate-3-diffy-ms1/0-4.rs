
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
			N > 0,
			i <= N as usize,
			a.len() == N, 
			sum.len() == 1,
			old(a).len() == N,
			old(sum).len() == 1,
			forall |j:int| 0 <= j < i ==> a[j] == j % 1,
	{
		a.set(i, i % 1);
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			N > 0,
			i <= N as usize,
			a.len() == N, 
			sum.len() == 1,
			old(a).len() == N,
			old(sum).len() == 1,
			forall |j:int| 0 <= j < N ==> a[j] == j % 1, // to support function post-condition
			sum[0] == a[( 0..i ) as int].iter().sum(),
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2