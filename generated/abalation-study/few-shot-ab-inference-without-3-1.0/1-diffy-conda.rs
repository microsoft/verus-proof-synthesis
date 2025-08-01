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

	while (i < N as usize)
		invariant
			i <= N as usize,
			N < 1000,
			a.len() == N,
			forall |k: int| 0 <= k && k < i as int ==> a[k] == 1,
			forall |k: int| i <= k && k < N as int ==> a[k] == old(a)[k],
	{
		a.set(i, 1);
        i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N < 1000,
	        a.len() == N,
	    	forall |k: int| 0 <= k && k < i as int ==> a[k] == 2,
            forall |k: int| i <= k && k < N as int ==> a[k] == 1,
	{
		if (a[i] == 1) {
			a.set(i, a[i] + 1);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			N < 1000,
	        sum.len() == 1,
	        a.len() == N,
        	forall |k: int| 0 <= k && k < N as int ==> a[k] == 2,
        	sum[0] == i as int * 2,
	{
		sum.set(0, sum[0] + a[i]);
        i = i + 1;
	}
}
}
// Score: (4, 0)
// Safe: True