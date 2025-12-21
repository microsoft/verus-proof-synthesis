use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
	ensures
		sum[0] == 0,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			forall |k: int| 0<= k < i ==> a[k] == 0,
			a.len() == N,
	{
		a.set(i, i % 1 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			forall |k: int| 0<= k < N ==> a[k] == 0,
			a.len() == N,
			i > 0 ==> sum[0] == 0,
			sum.len() == 1,
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
