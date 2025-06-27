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
        sum[0] == 2 * N,
{
	sum.set(0, 0);

	let mut i: usize = 0;
	while i < N as usize
        invariant
            // invariants for loop variables and lengths
            0 <= i <= N as usize,
            a@.len() == N as int,
            sum@.len() == 1,
            // invariant to ensure `a` is being set to 2 for all positions
            forall |k: int| 0 <= k < i as int ==> a[k] == 2,
	{
		a.set(i, 2);
		i = i + 1;
	}

	i = 0;
	while i < N as usize
        invariant
            // invariants for loop variables and lengths
            0 <= i <= N as usize,
            a@.len() == N as int,
            sum@.len() == 1,
            // invariant for correct sum accumulation
            sum[0] == 2 * i as i32,
            // invariant to ensure `a` is still all 2's
            forall |k: int| 0 <= k < N as int ==> a[k] == 2,
	{
		if a[i] == 2 {
			sum.set(0, sum[0] + a[i]);
		} else {
			sum.set(0, sum[0] * a[i]);
		}
		i = i + 1;
	}
}
}
// Score: (2, 2)
// Safe: False