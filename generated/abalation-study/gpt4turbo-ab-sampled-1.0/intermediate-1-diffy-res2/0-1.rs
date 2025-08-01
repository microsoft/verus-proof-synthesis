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
	        i <= N,
	        N < 1000,
	        a.len() == N,
	        forall |k:int| 0 <= k < i ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	    invariant
	        i <= N,
	        N < 1000,
	        a.len() == N,
	        b.len() == N,
	        sum[0] == i as i32,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	    invariant
	        i <= N,
	        N < 1000,
	        b.len() == N,
	        forall |k:int| 0 <= k < i ==> b[k] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	    invariant
	        i <= N,
	        N < 1000,
	        a.len() == N,
	        b.len() == N,
	        c.len() == N,
	        sum[0] == N + i as i32,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	    invariant
	        i <= N,
	        N < 1000,
	        c.len() == N,
	        forall |k:int| 0 <= k < i ==> c[k] == 1,
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
	    invariant
	        i <= N,
	        N < 1000,
	        a.len() == N,
	        b.len() == N,
	        c.len() == N,
	        sum[0] == 2 * N + i as i32,
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 4, Errors: 3, Verus Errors: 12