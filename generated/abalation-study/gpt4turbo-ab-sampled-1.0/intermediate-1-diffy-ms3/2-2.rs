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
    {
		a.set(i, (i % 3) as i32);
		i = i + 1;
	}

	i = 0;
	let mut local_sum: i32 = 0;
	while (i < N as usize)
	    invariant
	        i <= N as usize,
	        sum.len() == 1,
	        0 <= local_sum <= 2 * i as i32,
    {
		if (i == 0) {
			sum.set(0, 0);
		} else {
			local_sum = local_sum + a[i];
			sum.set(0, local_sum);
		}
		i = i + 1;
	}
}
}
// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 4