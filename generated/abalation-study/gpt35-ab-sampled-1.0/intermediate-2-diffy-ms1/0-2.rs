
use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_modulo_zero(k: usize) -> usize
    ensures
        k % 1 == 0,
{
    0
}

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
            N > 0,
            a.len() == N,
            sum.len() == 1,
            old(a).len() == N,
            old(sum).len() == 1,
            forall |j:int| 0 <= j < i ==> a[j] == j % 1,
	{
		a.set(i, i % 1 );
		i = i + 1;
	}

	i = 0;

	while (i < N as usize)
        invariant
            N > 0,
            sum.len() == 1,
            old(sum).len() == 1,
            forall |j:int| 1 <= j <= i ==> sum[j-1] + a[j] == sum[j],
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