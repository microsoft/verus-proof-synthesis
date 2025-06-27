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
		sum[0] == 6 * N,
{
	let mut i: usize = 0;
	sum.set(0, 0);

	while (i < N as usize)
        invariant 
            0 <= i <= N as usize,
            a.len() == N,
            forall |j: int| 0 <= j < i as int ==> a[j] == 1,
    {
		a.set(i, 1);
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant 
            0 <= i <= N as usize,
            a.len() == N,
            forall |j: int| 0 <= j < i as int ==> a[j] == 6,  // Every element set to 6 after second loop
            forall |j: int| i as int <= j < N as int ==> a[j] == 1,
    {
		if (a[i] == 1) {
			a.set(i, a[i] + 5);
		} else {
			a.set(i, a[i] - 1);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant 
            0 <= i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            sum[0] == 6 * (i as i32),  // Reflect sum for current i
            forall |j: int| 0 <= j < N as int ==> a[j] == 6,
    {
		sum.set(0, sum[0] + a[i]);
		i = i + 1;
	}
}
}
// Score: (3, 2)
// Safe: True