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
    
    // Initialize a with 1s
	while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            forall |k: int| 0 <= k < i as int ==> a[k] == 1,
	{
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
    // Initialize b with 1s
	while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            b.len() == N,
            forall |k: int| 0 <= k < i as int ==> b[k] == 1,
	{
		b.set(i, 1);
		i = i + 1;
	}

	i = 0;
    // Sum elements of a into sum[0]
	while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum.len() == 1,
            a.len() == N,
            sum[0] == i as i32,
            forall |k: int| 0 <= k < N ==> a[k] == 1,
	{
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}

	i = 0;
    // Sum elements of b into sum[0]
	while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum.len() == 1,
            b.len() == N,
            sum[0] == N + i as i32,
            forall |k: int| 0 <= k < N ==> a[k] == 1,
            forall |k: int| 0 <= k < N ==> b[k] == 1,
	{
		sum.set(0, sum[0] + b[i]);
		i = i + 1;
	}

	i = 0;
    // Update elements of a with the calculated sum
	while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            sum[0] == 2 * N,
            forall |k: int| 0 <= k < i as int ==> a[k] == 2 * N + 1,
            forall |k: int| i <= k < N ==> a[k] == 1,
	{
		a.set(i, a[i] + sum[0]);
		i = i + 1;
	}
}
}
// Score: (5, 2)
// Safe: True