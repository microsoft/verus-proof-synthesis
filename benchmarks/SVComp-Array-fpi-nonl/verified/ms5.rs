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
			forall |k:int| 0<= k < i ==> a[k] == k % 5,
			a.len() == N,
		decreases
			N - i,
	{
		a.set(i, (i % 5) as i32);
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			i <= N,
			forall |k:int| 0<= k < N ==> a[k] == k % 5,
			a.len() == N,
			i > 0 ==> sum[0] <= 4 * i,
			sum.len() == 1,
			N < 1000,
		decreases
			N - i,
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