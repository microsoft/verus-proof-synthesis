
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
		sum[0] == 4 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;
	while (i < N as usize)
        invariant 
            i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            N > 0,
            N < 1000,
            old(a).len() == N,
            old(sum).len() == 1,
        {
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant 
            i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            N > 0,
            N < 1000,
            old(a).len() == N,
            old(sum).len() == 1,
            forall |j: int| 0 <= j < i == > if a[j]==1 then a[j]==4 else a[j]==0, // the value of a[j] should be either 1+3 or 1-1
        {
		if (a[i] == 1) {
			a.set(i, a[i] + 3);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant 
            i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            N > 0,
            N < 1000,
            old(a).len() == N,
            old(sum).len() == 1,
            sum[0] == sum[0] + a[i], // the sum is being updated correctly
        {
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1