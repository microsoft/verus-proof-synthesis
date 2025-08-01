
use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(c).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		sum[0] <= 3 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;

	while (i < N as usize)
		invariant 
		    i <= N as usize,
		    N < 1000,
		    sum[0] >= 0,
		    a.len() == N,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
		    i <= N as usize,
		    sum[0] == i as i32,
		    a.len() == N,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant 
		    i <= N as usize,
		    sum[0] <= 2 * N as i32,
		    b.len() == N,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant 
		    i <= N as usize,
		    sum[0] <= 3 * N as i32,
		    c.len() == N,
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}

// is safe: False
// Score: Compilation Error: False, Verified: 3, Errors: 2, Verus Errors: 8