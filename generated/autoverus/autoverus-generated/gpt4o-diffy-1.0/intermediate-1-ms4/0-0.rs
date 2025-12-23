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
			old(a).len() == N,
			old(sum).len() == 1,
			N > 0,
			N < 1000,
			a.len() == N,
			sum.len() == 1,
			forall |j: int| 0 <= j < i ==> a[j as int] == (j % 4) as i32,
	{
		a.set(i, (i % 4) as i32);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			old(a).len() == N,
			old(sum).len() == 1,
			N > 0,
			N < 1000,
			a.len() == N,
			sum.len() == 1,
			forall |j: int| 0 <= j < i ==> 
				(if j == 0 { sum[0] == 0 } else { sum[0] <= 3 * j && sum[0] == sum[0] + a[j as int] }),
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
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3