
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
            a.len() == N as usize,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            sum[0] <= 1 * i,
            a.len() == N as usize,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            sum[0] <= 2 * i,
            a.len() == N as usize,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            sum[0] <= 3 * i,
            a.len() == N as usize,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            sum[0] <= 4 * i,
            a.len() == N as usize,
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            sum[0] <= 5 * i,
            a.len() == N as usize,
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 6, Verus Errors: 21