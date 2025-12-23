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
		sum[0] <= 3 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			N < 1000,
			a.len() == N,
			forall |k:int| 0 <= k < i ==> 
				(i % 3 == 0 ==> a[k as int] == 3) &&
				(i % 3 != 0 ==> a[k as int] == 0),
	{
		if (i % 3 == 0) {
			a.set(i, 3);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;

	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			N < 1000,
			a.len() == N,
			sum.len() == 1,
			if i > 0 {
				sum[0] == (sum[0] + sum[0] + a[( 0..i ) as int].iter().fold(0, |acc, &x| acc + x))
			},
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3