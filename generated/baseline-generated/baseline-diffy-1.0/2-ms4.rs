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
		0 <= i <= N as usize,
		a@.len() == N as int,
		sum@.len() == 1,
		forall |k: int| 0 <= k < i ==> (a[k] == k % 4),
	{
		a.set(i, (i % 4) as i32);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	invariant
		0 <= i <= N as usize,
		a@.len() == N as int,
		sum@.len() == 1,
		sum[0] <= 3 * i as int,
		forall |k: int| 0 <= k < N as int ==> (a[k] == k % 4),
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
// Score: (1, 2)
// Safe: True