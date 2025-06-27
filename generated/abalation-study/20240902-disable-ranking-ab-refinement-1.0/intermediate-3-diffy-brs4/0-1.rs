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
			i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			forall |k: int| 0 <= k < i ==> ( ( ) as bool
				(k % 4 == 0) ==> a[k as int] == 4,
				(k % 4 != 0) ==> a[k as int] == 0,
			),
	{
		if (i % 4 == 0) {
			a.set(i, 4);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			sum.len() == 1,
			a.len() == N,
			forall |k: int| 0 <= k < N ==> (
				(k % 4 == 0) ==> a[k as usize] == 4,
				(k % 4 != 0) ==> a[k as usize] == 0,
			),
			sum[0] <= 4 * (i as i32),
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



// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1