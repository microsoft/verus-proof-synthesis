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

	while i < N as usize
	invariant 
		0 <= i <= N as usize,
		a@.len() == N,  // length of vector a
		forall |k:int| 0 <= k < i ==> a[k] == 1, // all values up to i are set to 1
		// Old values of a are unchanged except for first i elements
		forall |k:int| i<=k<N as int ==> a[k]==old(a)[k]  // Added invariant: All a values from i onwards remain unchanged
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while i < N as usize
	invariant 
	 	0 <= i <= N as usize,
		a@.len() == N,  // length of vector a
		forall |k:int| 0 <= k < i ==> a[k] == 5,
		forall |k:int| i<=k<N as int ==> a[k]==1,  // Added invariant.
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 4);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}
	assert(forall|k:int| 0<=k<N as int==>a[k]==5);
	
	i = 0;
	while i < N as usize
	invariant 
		0 <= i <= N as usize,
		a@.len() == N,  // length of vector a
		sum@.len() == 1,  // length of sum vector
		sum[0]==5*(i as i32),  // sum count of processed items
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}
// Score: (3, 2)
// Safe: False