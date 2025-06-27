use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, N: u32)
	requires
		N > 0,
		old(a).len() == N,
	ensures
		forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
{
	let mut i: usize = 0;

	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N as usize,
			N > 0,
			forall |k:int| 0 <= k < i as int ==> a[k] == 0,
	{
		a.set(i, 0);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N as usize,
			forall |k:int| 0 <= k < i as int ==> a[k] % 2 == N as i32 % 2,
			forall |k:int| i as u32 <= k < N ==> a[k] == 0,  //to support function post-condition
	{
		if (N % 2 == 0) {
			a.set(i, a[i] + 2);
		} else {
			a.set(i, a[i] + 1);
		}
		i = i + 1;
	}
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2