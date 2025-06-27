use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		sum[0] <= N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			a.len() == N,
			forall |k:int| 0 <= k < i ==> (if k % 1 == 0 { a[k as int] == 1 } else { a[k as int] == 0 }),
	{
		if (i % 1 == 0) {
			a.set(i, 1);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			sum.len() == 1,
			a.len() == N,
			forall |k:int| 0 <= k < i ==> (if k == 0 { sum[0] == 0 } else { sum[0] <= k && sum[0] == sum[0] + a[k as int] }),
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