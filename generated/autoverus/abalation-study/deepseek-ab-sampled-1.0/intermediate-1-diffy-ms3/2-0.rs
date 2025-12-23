

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
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            N < 1000,
            i <= N,
            a.len() == N,
            sum.len() == 1,
            // Elements of 'a' are initialized with i % 3, ranging from 0 to 2
            forall |j: usize| j < i ==> a[( j ) as int] == (j % 3) as i32,
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            N < 1000,
            // 'sum[0]' accumulates the sum of 'a' elements, each at most 2
            sum[0] <= 2 * (i as i32),
            // At each step, 'sum[0]' is the sum of the first 'i' elements of 'a'
            sum[0] == a.subvec(0, i).fold(0, |acc, x| acc + x),
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