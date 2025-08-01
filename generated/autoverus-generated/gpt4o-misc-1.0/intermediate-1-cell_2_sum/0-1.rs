use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
	requires 
		old(a).len() == N,
		N <= 0x7FFF_FFFF,
	ensures
		sum <= 2 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			forall |k:int| 0 <= k < i ==> a[k] <= 2,
	{
		if (a[i] > 2) {
			a.set(i, 2);
		} 
		i = i + 1;
	}

	i = 0;
    let mut sum: u32 = 0;
	
	while (i < N as usize)
		invariant
			i <= N as usize,
			sum <= 2 * N,
			forall |k:int| 0 <= k < N ==> a[k] <= 2,
			forall |k:int| 0 <= k < i ==> sum == a.subrange(0, i as int).fold(0, |acc, &x| acc + x),
	{
        sum = sum + a[i];
		i = i + 1;
	}

	sum
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1