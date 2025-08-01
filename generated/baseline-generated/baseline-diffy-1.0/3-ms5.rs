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
		sum[0] <= 4 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
		a.len() == N,
	{
		a.set(i, (i % 5) as i32);
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
		sum.len() == 1,
		(0 < i ==> sum[0] <= i as i32 * 4),
	{
		if i == 0 {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;
	}
}
}
// Score: (2, 2)
// Safe: False