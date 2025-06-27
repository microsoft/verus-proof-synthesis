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
		sum[0] <= 5 * N,
{
	let mut i: usize = 0;

	while (i < N as usize)
        invariant
            i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == if k % 5 == 0 { 5 } else { 0 }
	{
		if (i % 5 == 0) {
			a.set(i, 5);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
        invariant
            i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            sum.len() == 1,
            // For post-condition in function: only consider possibilities to sum[k]
            sum[0] <= 5 * N,
            forall |k:int| 0 <= k < i ==> sum[0] == (a.map(|x: i32| if x % 5 == 0 { 5 } else { 0 })).subrange(0, k).fold(0, |accum, x| accum + x) 
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
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1