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
            i <= N,
            a.len() == N,
            sum.len() == 1,
            forall |j:int| 0<= j < i ==> a[j] == j % 1,
            N > 0,
    {
        a.set(i, i % 1 );
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            N > 0,
            forall |j:int| 0<= j < N ==> a[j] == j % 1,
            // array `a` is not modified in the loop
            i > 0 ==> sum[0] == (0..i).fold(0, |acc, k| acc + a[k]),
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