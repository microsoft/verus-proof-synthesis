
use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_sum_initialization(sum: Seq<usize>) 
    ensures
        sum.len() > 0 ==> sum[0] == 0,
{
    assert(sum.len() == 1 ==> sum[0] == 0);
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
    assert(sum@.len() == 1 && sum[0] == 0);
	while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            sum.len() == 1,
	{
		a.set(i, i % 2 );
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
        invariant
            i <= N as usize,
            sum.len() == 1,
            N > 0,
            forall |j:int| 0 < j <= i ==> sum[j] == a[j],
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;
	}

    proof {
        lemma_sum_initialization(sum@);
    }
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 6