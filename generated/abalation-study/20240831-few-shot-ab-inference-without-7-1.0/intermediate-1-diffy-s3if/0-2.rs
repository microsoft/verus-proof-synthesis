use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] == 3 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N as usize,
			sum.len() == 1,
			forall |j: usize| 0 <= j < i ==> a[( j ) as int] == 3,
			forall |j: usize| i <= j < a.len() ==> old(a)[( j ) as int] == a[( j ) as int],
	{
		a.set(i, 3);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N as usize,
			sum.len() == 1,
			sum[0] <= 3 * i,
			forall |j: usize| 0 <= j < i ==> a[( j ) as int] == 3,
	{
		if (a[i] == 3) {
			sum.set(0, sum[0] + a[i]);
		} else {
			sum.set(0, sum[0] * a[i]);
		}
		i = i + 1;
	}
	assert(sum[0] == 3 * N);
}
}




// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5