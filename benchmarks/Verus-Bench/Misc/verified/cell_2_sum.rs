use vstd::prelude::*;
fn main() {}
verus!{

pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
	requires 
		old(a).len() == N,
		N <= 0x7FFF_FFFF,
	ensures
	    sum <= 2*N,
{
	let mut i: usize = 0;
	while (i < N as usize)
	invariant 
	    a.len()==N,
	    forall|j:int| 0<=j<i ==> a[j]<=2,
	{
		if (a[i] > 2) {
			a.set(i, 2);
		} 
		i = i + 1;
	}


	i = 0;
    let mut sum: u32 = 0;
	
	while (i < N as usize)
	invariant
	    i<=N,
	    N <= 0x7FFF_FFFF,
	    a.len()==N,
	    forall|j:int| 0<=j<N ==> a[j]<=2,
	    sum<=2 * i,
	{
        sum = sum + a[i];
		i = i + 1;
	}

    sum

}
}
