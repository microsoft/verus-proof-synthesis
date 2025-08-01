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
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			0 < N < 1000,
			forall |j: int| 0 <= j < i ==> (if j % 2 == 0 { a[j] == 2 } else { a[j] == 0 }),
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
			i <= N as usize,
			sum.len() == 1,
			a.len() == N,
			0 < N < 1000,
			forall |j: int| 0 <= j < i ==> (sum[0] >= 0 && sum[0] == a.subrange(0, i as int).fold(|acc, x| acc + x, 0)),
			forall |j: int| 0 <= j < i ==> (if j % 2 == 0 { a[j] == 2 } else { a[j] == 0 }),
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;
	}

	// Ensure postcondition holds
	assert(sum[0] <= 2 * N);
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1