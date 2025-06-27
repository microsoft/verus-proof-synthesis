use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
		N < 1000,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] == 2 * N + 1,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < i ==> a[k] == 1,
            forall |k:int| i <= k < N ==> a[k] == old(a)[k],
            sum[0] == 0,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < i ==> b[k] == 1,
            forall |k:int| i <= k < N ==> b[k] == old(b)[k],
            sum[0] == 0,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < N ==> b[k] == 1,
            forall |k:int| 0 <= k < N ==> a[k] == 1,
            sum[0] == (i as i32) * 1,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < N ==> b[k] == 1,
            forall |k:int| 0 <= k < N ==> a[k] == 1,
            sum[0] == N,
            sum[0] + sum[0] == N + (i as i32) * 1,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < N ==> b[k] == 1,
            forall |k:int| 0 <= k < i ==> a[k] == 2 * N + 1,
            forall |k:int| i <= k < N ==> a[k] == 1,
            sum[0] == 2 * N,
	{
		a.set(i, a[i] + sum[0]);
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 5, Errors: 1, Verus Errors: 2