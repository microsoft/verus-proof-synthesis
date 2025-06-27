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
		sum[0] <= 3 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant 
			0 <= i <= N as usize,
			old(a).len() == N,
			old(sum).len() == 1,
			a@.len() == N as int,
			forall |j: int| 0 <= j < i as int ==> (a@[j] == (j % 4) as i32),
	{
		a.set(i, (i % 4) as i32);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			0 <= i <= N as usize,
			old(a).len() == N,
			old(sum).len() == 1,
			a@.len() == N as int,
			forall |j: int| 0 <= j < N as int ==> (a@[j] == (j % 4) as i32),
			sum@.len() == 1,
			if i == 0 { sum[0] == old(sum)[0] } else { sum[0] == (i as i32 - 1) / 4 * 6 + (i as i32 % 4 * (i as i32 % 4 + 1)) / 2 },
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
// Score: (1, 3)
// Safe: True