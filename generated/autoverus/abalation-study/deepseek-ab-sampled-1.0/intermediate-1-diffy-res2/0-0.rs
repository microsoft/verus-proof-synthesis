

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

    // Loop 1: Initialize vector a
    while (i < N as usize)
        invariant
            N < 1000,
            i <= N,
            a.len() == N,
            sum[0] == 0,
            // Invariant: All elements of a up to current i are 1, others as old
            forall |k: i32| 0 <= k < i as i32 ==> a[k] == 1,
    {
        a.set(i, 1);
        i += 1;
    }

    // Loop 2: Sum vector a
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            i <= N,
            a.len() == N,
            sum[0] == (i as i32) * 1,
            // Invariant: sum[0] increases by 1 for each iteration
            forall |k: i32| 0 <= k < N ==> if k < i as i32 then a[k] == 1 else a[k] == old(a)[k],
    {
        sum.set(0, sum[0] + a[i]);
        i += 1;
    }

    // Loop 3: Initialize vector b
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            i <= N,
            b.len() == N,
            sum[0] == N,
            // Invariant: All elements of b up to current i are 1, others as old
            forall |k: i32| 0 <= k < i as i32 ==> b[k] == 1,
    {
        b.set(i, 1);
        i += 1;
    }

    // Loop 4: Sum vector b
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            i <= N,
            b.len() == N,
            sum[0] == N + (i as i32) * 1,
            // Invariant: sum[0] increases by 1 for each iteration
            forall |k: i32| 0 <= k < N ==> if k < i as i32 then b[k] == 1 else b[k] == old(b)[k],
    {
        sum.set(0, sum[0] + b[i]);
        i += 1;
    }

    // Loop 5: Initialize vector c
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            i <= N,
            c.len() == N,
            sum[0] == 2 * N,
            // Invariant: All elements of c up to current i are 1, others as old
            forall |k: i32| 0 <= k < i as i32 ==> c[k] == 1,
    {
        c.set(i, 1);
        i += 1;
    }

    // Loop 6: Sum vector c
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            i <= N,
            c.len() == N,
            sum[0] == 2 * N + (i as i32) * 1,
            // Invariant: sum[0] increases by 1 for each iteration
            forall |k: i32| 0 <= k < N ==> if k < i as i32 then c[k] == 1 else c[k] == old(c)[k],
    {
        sum.set(0, sum[0] + c[i]);
        i += 1;
    }
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1