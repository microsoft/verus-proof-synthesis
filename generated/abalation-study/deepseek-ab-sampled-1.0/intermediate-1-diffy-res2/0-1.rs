

use vstd::prelude::*;
fn main() {}

verus! {

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
			old(a).len() == N,
			forall |k: int| 0 <= k < i ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			sum[0] == (i) as i32, // Because each a[j] ==1
			forall |k: int| 0 <= k < i ==> a[k] ==1,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N,
			forall |k: int| 0 <= k < i ==> b[k] ==1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	let mut j: usize = 0;
	while (j < N as usize)
		invariant
			j <= N,
			sum[0] == (i) as i32 + (j) as i32, // i is N, since previous loop finished, this represents sum of a being N, adding j of b
			forall |k: int| 0 <= k < j ==> b[k] ==1,
	{
		sum.set(0, sum[0] + b[j]);
		j = j + 1;
	}

	let mut k: usize = 0;
	while (k < N as usize)
		invariant
			k <= N,
			forall |m: int| 0 <= m < k ==> c[m] ==1,
	{
		c.set(k, 1);
		k = k + 1;
	}

	let mut l: usize = 0;
	while (l < N as usize)
		invariant
			l <= N,
			sum[0] == (i) as i32 + (j) as i32 + (l) as i32, // i and j are N, summing c now
			forall |m: int| 0 <= m < l ==> c[m] ==1,
	{
		sum.set(0, sum[0] + c[l]);
		l = l + 1;
	}
}
}

// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 6, Verus Errors: 24