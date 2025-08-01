

use vstd::prelude::*;
fn main() {}

verus! {

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

    // First loop: initialize a to 1s
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            sum[0] == 0,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;

    // Second loop: sum a
    while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            sum[0] == i as i32,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;

    // Third loop: initialize b to 1s
    while (i < N as usize)
        invariant
            i <= N,
            b.len() == N,
            sum.len() == 1,
            sum[0] == N as i32,
            forall |k: int| 0 <= k < i ==> b[k] == 1,
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;

    // Fourth loop: sum b
    while (i < N as usize)
        invariant
            i <= N,
            b.len() == N,
            sum.len() == 1,
            sum[0] == N as i32 + i as i32,
            forall |k: int| 0 <= k < i ==> b[k] == 1,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }

    i = 0;

    // Fifth loop: initialize c to 1s
    while (i < N as usize)
        invariant
            i <= N,
            c.len() == N,
            sum.len() == 1,
            sum[0] == 2 * (N as i32),
            forall |k: int| 0 <= k < i ==> c[k] == 1,
    {
        c.set(i, 1);
        i = i + 1;
    }

    i = 0;

    // Sixth loop: sum c
    while (i < N as usize)
        invariant
            i <= N,
            c.len() == N,
            sum.len() == 1,
            sum[0] == 2 * (N as i32) + i as i32,
            forall |k: int| 0 <= k < i ==> c[k] == 1,
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 4, Errors: 3, Verus Errors: 9