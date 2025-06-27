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
		sum[0] <= 5 * N,
{
	let mut i: usize = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			a.len() == N,
			forall |j: int| 0 <= j < i ==> if j % 5 == 0 { a[j as int] == 5 } else { a[j as int] == 0 },
	{
		if (i % 5 == 0) {
			a.set(i, 5);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
		invariant
			i <= N as usize,
			sum.len() == 1,
			a.len() == N,
			forall |j:int| 0 <= j < i ==> if j == 0 { sum[0] == 0 } else { sum[0] == seqsum(0, j as int + 1, |k: int| a[k as int]) },
			sum[0] <= 5 * N,
	{
		if (i == 0) {
			sum.set(0, 0);
		} else {
			sum.set(0, sum[0] + a[i]);
		}
		i = i + 1;
	}
}

fn seqsum(start: int, end: int, f: impl Fn(int) -> i32) -> i32 {
    let mut sum: i32 = 0;
    let mut i = start;
    while i < end {
        sum += f(i);
        i += 1;
    }
    sum
}
}



// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1