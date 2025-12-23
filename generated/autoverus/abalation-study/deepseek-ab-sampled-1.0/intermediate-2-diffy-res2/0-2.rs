
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
			b.len() == N as usize,
			c.len() == N as usize,
			sum.len() == 1,
			old(a).len() == N as usize,
			old(b).len() == N as usize,
			old(c).len() == N as usize,
			forall |k: usize| k < i ==> a[( k ) as int] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant 
            i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            c.len() == N as usize,
            sum.len() == 1,
            old(a).len() == N as usize,
            old(b).len() == N as usize,
            old(c).len() == N as usize,
            forall |k: usize| k < i ==> a[( k ) as int] == 1,
            old(i < N).implies(sum[0] == i + old(sum)[0]),
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant 
            i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            c.len() == N as usize,
            sum.len() == 1,
            old(a).len() == N as usize,
            old(b).len() == N as usize,
            old(c).len() == N as usize,
            forall |k: usize| k < i ==> b[k] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant 
            i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            c.len() == N as usize,
            sum.len() == 1,
            old(a).len() == N as usize,
            old(b).len() == N as usize,
            old(c).len() == N as usize,
            forall |k: usize| k < i ==> b[k] == 1,
            old(i < N).implies(sum[0] == old(sum)[0] + i),
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant 
            i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            c.len() == N as usize,
            sum.len() == 1,
            old(a).len() == N as usize,
            old(b).len() == N as usize,
            old(c).len() == N as usize,
            forall |k: usize| k < i ==> c[k] == 1,
	{
		c.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant 
            i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            c.len() == N as usize,
            sum.len() == 1,
            old(a).len() == N as usize,
            old(b).len() == N as usize,
            old(c).len() == N as usize,
            forall |k: usize| k < i ==> c[k] == 1,
            old(i < N).implies(sum[0] == old(sum)[0] + i),
	{
		sum.set(0, sum[0] + c[i]);
		i = i + 1;
	}
}
}



// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 7