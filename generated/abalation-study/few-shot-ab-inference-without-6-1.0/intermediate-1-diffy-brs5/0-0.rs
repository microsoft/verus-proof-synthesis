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
			0 <= i <= N as usize,
			a.len() == N as usize,
			sum.len() == 1,
			N > 0,
			N < 1000,
			forall |j: int| 0 <= j < i ==> a[j] == if j % 5 == 0 { 5 } else { 0 },
			forall |j: int| i <= j < N as usize ==> old(a)[j] == a[j],
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
			0 <= i <= N as usize,
			a.len() == N as usize,
			sum.len() == 1,
			N > 0,
			N < 1000,
			sum[0] <= 5 * N,
			forall |j: int| 0 <= j < i ==> sum[0] == sum[0] + a[j],
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
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1