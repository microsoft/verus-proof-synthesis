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
		sum[0] <= 2 * N,
{
	let mut i: usize = 0;
	proof {
		assert(N > 0);
		assert(N < 1000);
		assert(old(sum).len() == 1);
	}
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
		a.len() == N,
		old(sum).len() == 1,
		old(a).len() == N,
		N > 0,
		N < 1000,
		true,
	{
		if (i % 2 == 0) {
			a.set(i, 2);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
        sum.len() == 1,
		a.len() == N,
		old(sum).len() == 1,
		i > 0 ==> sum[0] <= 2 * (i - 1) as i32,
		true,
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;
	}
	assert(sum[0] <= 2 * N);
}
}
// Score: (2, 2)
// Safe: True