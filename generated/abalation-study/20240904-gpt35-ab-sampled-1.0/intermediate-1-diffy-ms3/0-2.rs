
use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_sum_at_k(k: usize, sum: &Vec<i32>, a: &Vec<i32>)
    requires
        sum.len() == 1,
        old(sum).len() == 1,
        forall |j:usize| 0<= j < k && j < a.len() ==> a[( j ) as int] < 3,
    ensures
        sum[0] <= 2 * k as i32,
{
    let mut s: i32 = 0;
    for j in 0..k {
        s = s + a[( j ) as i32;
    }
    assert(s <= 2 * k as i32);
}

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
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
			i <= N as usize,
			N > 0,
			N < 1000,
			a.len() == N as usize,
			sum.len() == 1,
			forall |j:usize| 0<= j < i && j < a.len() ==> a[j] < 3,
	{
		a.set(i, (i % 3) as i32);
		i = i + 1;
	}

	i = 0;
	
	while (i < N as usize)
		invariant
			i <= N as usize,
			N > 0,
			N < 1000,
			a.len() == N as usize,
			sum.len() == 1,
			forall |j:usize| 0<= j < i && j < a.len() ==> a[j] < 3,
			(old(i) > 0 ==> sum[0] <= 2 * (i - 1) as i32), //to support function post-condition
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;

		proof {
			lemma_sum_at_k(i, sum, a);
		}
	}
}
} 




// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1