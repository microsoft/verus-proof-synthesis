
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
	let mut i: usize = 0; //a mutable variable to iterate over elements

	while (i < N as usize)
		invariant
			i <= N,
			old(a).len() == N,
	{
		a.set(i, i % 1 ); //setting the value of a[i] to i % 1
		i = i + 1;
	}

	i = 0; //reset the value of i to 0 for second while loop

	while (i < N as usize)
		invariant
			i <= N,
			old(sum).len() == 1,
			forall |j: int| 0 <= j < i ==> a[j] == j % 1
	{
		if (i == 0) {
			sum.set(0, 0); //setting the value of sum[0] to 0 if i is 0
		} else {
			sum.set(0, sum[0] + a[i]); //adding the value of a[i] to sum[0]
		}
		i = i + 1;
	}
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 8