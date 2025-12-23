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
			0 <= i <= N,
			a.len() == N,
			i <= a.len(),
			forall |j: usize| 0 <= j < i ==> (a[( j ) as int] == 5 || a[( j ) as int] == 0),
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
			0 <= i <= N,
			sum.len() == 1,
			i <= a.len(),
			sum[0] <= 5 * i,
			forall |j: usize| 0 <= j < i ==> (a[( j ) as int] == 5 || a[( j ) as int] == 0),
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
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 6