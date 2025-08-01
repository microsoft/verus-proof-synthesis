
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(c).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    
    while (i < N as usize)
        invariant
            N < 1000,
            i <= N,
            a.len() == N,
            forall |k:i32| 0 <= k < i as i32 ==> a[k] == 1,
        {
            a.set(i, 1);
            i = i + 1;
        }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            sum[0] == seq::sum(a[..i]),
            a.len() == N,
        {
            sum.set(0, sum[0] + a[i]);
            i = i + 1;
        }

    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            i <= N,
            b.len() == N,
            forall |k: i32| 0 <= k < i as i32 ==> b[k] == 1,
        {
            b.set(i, 1);
            i = i + 1;
        }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            sum[0] == seq::sum(a) + seq::sum(b[..i]),
            b.len() == N,
            a.len() == N,
        {
            sum.set(0, sum[0] + b[i]);
            i = i + 1;
        }

    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            i <= N,
            c.len() == N,
            forall |k: i32| 0 <= k < i as i32 ==> c[k] == 1,
        {
            c.set(i, 1);
            i = i + 1;
        }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N,
            sum[0] == seq::sum(a) + seq::sum(b) + seq::sum(c[..i]),
            c.len() == N,
        {
            sum.set(0, sum[0] + c[i]);
            i = i + 1;
        }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 6