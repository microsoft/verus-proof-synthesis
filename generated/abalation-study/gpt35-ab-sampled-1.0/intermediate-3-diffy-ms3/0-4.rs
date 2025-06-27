
use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 2 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
            i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            N > 0, N < 1000,
            old(a).len() == N,
            old(sum).len() == 1,
            forall |k:int| 0 <= k < i ==> a[k] == (k % 3) as i32,
            if i > 0 { sum[0] >= (i - 1) / 3 },
	{
		a.set(i, (i % 3) as i32);
		i = i + 1;
	}

	i = 0;
	
    invariant
        i <= N as usize,
        a.len() == N as usize,
        sum.len() == 1,
        N > 0, N < 1000,
        old(a).len() == N,
        old(sum).len() == 1,
        sum[0] <= 2 * (i as i32),
        forall |k:int| 0 <= k < i ==> a[k] == (k % 3) as i32,  //to support function post-condition
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;
	}
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1