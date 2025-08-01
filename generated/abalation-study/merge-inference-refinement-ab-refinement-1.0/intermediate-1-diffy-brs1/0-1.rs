use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
	requires
		N > 0,
		old(a).len() == N,
		old(sum).len() == 1,
	ensures
		sum[0] <= N,
{
	let mut i: usize = 0;
	while (i < N as usize)
        invariant
            0 <= N,
            N < 1000, // since we need only positive N for ensures and requires
            a.len() == N,
            i <= N as usize,
            forall |k:int| 0 <= k < i ==> if k % 1 == 0 { a[k] == 1 } else { a[k] == 0 },
	{
		if (i % 1 == 0) {
			a.set(i, 1);
		} else {
			a.set(i, 0);
		}
		i = i + 1;
	}

	i = 0;
	while (i < N as usize)
        invariant
            0 <= N,
            N < 1000, // since we need only positive N for ensures and requires
            sum.len() == 1,
            a.len() == N,
            i <= N as usize,
            forall |k:int| 0 <= k < N ==> if k % 1 == 0 { a[k] == 1 } else { a[k] == 0 },
            forall |k:int| 0 <= k < i ==> sum[0] <= N,
	isolated i => (i == 0) ==> sum[0] == 0,
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
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1