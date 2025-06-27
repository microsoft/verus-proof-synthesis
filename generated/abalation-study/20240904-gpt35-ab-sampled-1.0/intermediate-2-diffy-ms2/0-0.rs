
use vstd::prelude::*;
fn main() {}
verus!{
proof fn lemma_sum_update(a: &mut Vec<usize>, i: usize, sum: &mut Vec<usize>)
    requires
        i > 0,
        old(sum).len() == 1,
        old(a).len() >= i,
    ensures
        sum[( i ) as int] == old(sum)[0] + (a[( i ) as int]),
{
    assert(i > 0);
    assert(old(sum).len() == 1);
    assert(old(a).len() >= i);
    sum.set(0, old(sum)[0] + a[( i ) as usize);
}

pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
	ensures
		sum[0] <= N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
	{
		a.set(i, i % 2 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			sum.len() == 1,
			N > 0,
			if i > 0 { sum[0] >= i },
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			lemma_sum_update(a, i, sum);
		}
		i = i + 1;
	}
}
}





// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1