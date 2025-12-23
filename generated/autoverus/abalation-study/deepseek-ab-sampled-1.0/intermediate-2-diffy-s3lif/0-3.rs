

use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    
    while (i < N as usize)
        invariant
            N > 0,
            i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            sum[0] == 0,
            forall |k:i32| 0 <= k < i as i32 ==> a[k as int] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            sum[0] == 0,
            forall |k:i32| 0 <= k < i as i32 ==> a[k as int] == 4,
            forall |k:i32| i as i32 <= k < N ==> a[k as int] == 1,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            sum[0] == 4 * i as i32,
            forall |k:i32| 0 <= k < N ==> a[k as int] == 4,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}




// is safe: True
// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 2