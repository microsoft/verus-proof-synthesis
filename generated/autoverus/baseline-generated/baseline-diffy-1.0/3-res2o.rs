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
    let mut i: usize = 0;
    sum.set(0, 0);

    // Loop to set all elements of a to 1
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            forall |k:int| 0 <= k < i ==> a[k] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;

    // Loop to set all elements of b to 1
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            b.len() == N,
            forall |k:int| 0 <= k < i ==> b[k] == 1,
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;

    // Loop to set all elements of c to 1
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            c.len() == N,
            forall |k:int| 0 <= k < i ==> c[k] == 1,
    {
        c.set(i, 1);
        i = i + 1;
    }

    i = 0;

    // Loop to calculate the sum of elements in a
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            sum[0] <= i as i32,
            forall |k:int| 0 <= k < N ==> a[k] == 1,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;

    // Loop to calculate the sum of elements in b
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            b.len() == N,
            sum.len() == 1,
            sum[0] <= N + i as i32,
            forall |k:int| 0 <= k < N ==> b[k] == 1,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }

    i = 0;

    // Loop to calculate the sum of elements in c
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            c.len() == N,
            sum.len() == 1,
            sum[0] <= 2 * N + i as i32,
            forall |k:int| 0 <= k < N ==> c[k] == 1,
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}
}
// Score: (5, 2)
// Safe: False