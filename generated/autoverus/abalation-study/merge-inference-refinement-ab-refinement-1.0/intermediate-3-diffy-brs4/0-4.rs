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
		sum[0] <= 4 * N,
{
	let mut i: usize = 0;

	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			N < 1000,
			a.len() == N,
			sum.len() == 1,
			forall |j: int| 0 <= j < i ==> if j % 4 == 0 { a[j as int] == 4 } else { a[j as int] == 0 },
	{
		if (i % 4 == 0) {
			a.set(i, 4);
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
			forall |j: int| 0 <= j < N ==> if j % 4 == 0 { a[j as int] == 4 } else { a[j as int] == 0 }, // The array a is not changed in this loop
			forall |j: int| 0 <= j < i ==> sum[0] == a.subrange(0, j + 1).filter(|x| *x == 4).len() * 4,
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