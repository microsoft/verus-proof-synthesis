
use vstd::prelude::*;
fn main() {}

verus! {
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
            i <= N, // Ensuring the loop does not exceed N iterations
            a.len() == N, // Maintaining the length of 'a'
            sum.len() == 1, // Maintaining the length of 'sum'
            forall |k: usize| k < i ==> a[( k ) as int] == 0, // All elements before index 'i' are zero
    {
        a.set(i, i % 1 ); // Equivalent to setting each element to 0
        i = i + 1;
    }

    i = 0;
    
    while (i < N as usize)
        invariant 
            i <= N, // Ensuring the loop does not exceed N iterations
            a.len() == N, // Maintaining the length of 'a'
            sum.len() == 1, // Maintaining the length of 'sum'
            forall |k: usize| k < i ==> a[( k ) as int] == 0, // All elements in 'a' are zero up to index 'i'
            sum[0] == 0, // Ensuring 'sum[0]' remains zero
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
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3