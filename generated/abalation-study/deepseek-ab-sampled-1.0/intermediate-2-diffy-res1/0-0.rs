

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
		sum[0] <= 2 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	// Loop 1: Set a to 1
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			forall |k: int| 0 <= k < i ==> a[k] == 1,
		.likes(Seq::new(N, |j: int| if j < i then 1 else /*unchanged*/ a[j]))
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	// Loop 2: Set b to 1
	while (i < N as usize)
		invariant
			i <= N as usize,
			b.len() == N,
			forall |k: int| 0 <= k < i ==> b[k] == 1,
		.likes(Seq::new(N, |j: int| if j < i then 1 else /*unchanged*/ b[j]))
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
	// Loop 3: Add a to sum
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			sum[0] == i as i32,  // Since a[i] is 1, sum increases by 1 each iteration
			// Alternatively, if using seq:
			sum@ == Seq::new(1, |j: int| if j == 0 then i as i32 else 0)
	{
		sum.set(0, sum[0] + 1);
		i = i + 1;
	}

	i = 0;
	// Loop 4: Add b to sum
	while (i < N as usize)
		invariant
			i <= N as usize,
			b.len() == N,
			sum[0] == N + i as i32,  // Since sum was already N, and b[i] is 1
			// Alternatively, using seq:
			sum@ == Seq::new(1, |j: int| if j == 0 then N + i as i32 else 0)
	{
		sum.set(0, sum[0] + 1);
		i = i + 1;
	}
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1