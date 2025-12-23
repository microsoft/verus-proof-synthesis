
use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_sum_zero() 
    ensures
        Seq::<i32>::new(1, |i: int| 0).sum() == 0,
{
    assert(Seq::<i32>::new(1, |i: int| 0).sum() == 0);
}

pub fn myfun(a: &mut Vec<i32>, sum: &mut Seq<i32>, N: i32) 
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	ensures
		sum[0] <= 2 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			N > 0,
			N < 1000,
			i <= N,
			a.len() == N,
			sum.len() == 1,
			sum[0] <= 2 * N,
	{
		a.set(i, (i % 3) as i32);
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			N > 0,
			N < 1000,
			i <= N,
			a.len() == N,
			sum.len() == 1,
			sum[0] <= 2 * N,
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;

		proof {
            lemma_sum_zero();
        }
	}
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 5