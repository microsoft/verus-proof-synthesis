
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
            a.len() == b.len() == c.len() == N as usize,
            sum.len() == 1,
            N < 1000,
            sum[0] <= 3 * i as i32, // accumulated sum for array a
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == b.len() == c.len() == N as usize,
            sum.len() == 1,
            N < 1000,
            sum[0] <= 3 * N, // accumulated sum for array a and b
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == b.len() == c.len() == N as usize,
            sum.len() == 1,
            N < 1000,
            sum[0] <= 3 * N, // accumulated sum for array a, b, and c
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == b.len() == c.len() == N as usize,
            sum.len() == 1,
            N < 1000,
            sum[0] <= 3 * N,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == b.len() == c.len() == N as usize,
            sum.len() == 1,
            N < 1000,
            sum[0] <= 3 * N,
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == b.len() == c.len() == N as usize,
            sum.len() == 1,
            N < 1000,
            sum[0] <= 3 * N,
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 3, Errors: 4, Verus Errors: 7