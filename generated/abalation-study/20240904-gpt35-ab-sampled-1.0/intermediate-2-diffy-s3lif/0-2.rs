
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
		sum[0] == 4 * N,
{
	sum.set(0, 0);
	let mut i: usize = 0;

	while (i < N as usize)
        invariant
            N > 0,
            i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1, // Support function post-condition
            sum[0] == 0,
            forall |k:int| 0 <= k < i ==> a[k] == 1,
        {
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            N < 1000,
            sum[0] == a[( ..i ) as int].iter().sum::<i32>(), // Support function post-condition
            forall |k:int| 0 <= k < i ==> a[k] == 1, // Support function post-condition
        {
		if (a[i] == 1) {
			a.set(i, a[i] + 3);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            sum[0] == a[..i].iter().sum::<i32>(), // Support function post-condition
        {
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}


// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4