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
	        N > 0,
	        N < 1000,
	        a.len() == N,
	        forall |k: int| 0 <= k < i as int ==> a[k] == (k % 3) as i32,
	{
		a.set(i, (i % 3) as i32);
		i = i + 1;
	}

	i = 0;

    let mut local_sum: i32 = 0;
    
	while (i < N as usize)
	    invariant
	        i <= N as usize,
	        a.len() == N,
	        local_sum == sum[0],
	        local_sum <= 2 * i as i32, // Ensure sum calculation correctness
	        sum.len() == 1,
	        forall |k: int| 0 <= k < i as int ==> a[k] == (k % 3) as i32,
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
        local_sum = sum[0]; // Sync the local sum
		i = i + 1;
	}
}
}
// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4