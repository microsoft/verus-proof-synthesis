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
			a.len() == N as usize,
			sum.len() == 1,
			old(a).len() == N,
			old(sum).len() == 1,
			N > 0,
			N < 1000,
			forall |j: usize| 0 <= j && j < i ==> 
				if j % 3 == 0 { a[( j ) as int] == 3 } else { a[( j ) as int] == 0 },
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
			a.len() == N as usize,
			sum.len() == 1,
			sum[0] <= 3 * N,
			old(a).len() == N,
			old(sum).len() == 1,
			N > 0,
			N < 1000,
			if i > 0 { sum[0] == sum[0] + a[i-1] } else { sum[0] == old(sum)[0] },
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
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4