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

	while i < N as usize
		invariant
			i <= N,
			N > 0,
			N < 1000,
			a.len() == N,
			forall |k:int| 0 <= k < i ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while i < N as usize
		invariant
			i <= N,
			b.len() == N,
			forall |k:int| 0 <= k < i ==> b[k] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while i < N as usize
		invariant
			i <= N,
			sum.len() == 1,
			forall |k:int| 0 <= k < i ==> sum[0] == k,
			forall |k:int| 0 <= k < i ==> sum[0] == old(sum)[0] + old(a)[( 0..k ) as int].iter().fold(0, |acc, &x| acc + x),
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while i < N as usize
		invariant
			i <= N,
			sum.len() == 1,
			forall |k:int| 0 <= k < i ==> sum[0] == N as i32 + k,
			forall |k:int| 0 <= k < i ==> sum[0] == old(sum)[0] + old(a)[0..N as usize].iter().fold(0, |acc, &x| acc + x) + old(b)[0..k].iter().fold(0, |acc, &x| acc + x),
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
	while i < N as usize
		invariant
			i <= N,
			a.len() == N,
			sum.len() == 1,
			forall |k:int| 0 <= k < i ==> a[k] == 2 * N + 1,
	{
		a.set(i, a[i] + sum[0]);
		i = i + 1;
	}
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6