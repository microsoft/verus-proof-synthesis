use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] == N + 1,
{
    sum.set(0, 0);
    let mut i: usize = 0;

    // first loop: set all elements of a to 1
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            forall |k:int| 0 <= k < i as int ==> a[k] == 1
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;

    // second loop: set all elements of b to 1
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            b.len() == N,
            forall |k:int| 0 <= k < i as int ==> b[k] == 1
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;

    // third loop: sum up all elements in a and store in sum[0]
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum.len() == 1,
            a.len() == N,
            sum[0] == i as i32,
            forall |k:int| 0 <= k < N as int ==> a[k] == 1
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;

    // fourth loop: set all elements of a to b[i] + sum[0]
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            sum.len() == 1,
            b.len() == N,
            a.len() == N,
            sum[0] == N,
            forall |k:int| 0 <= k < i as int ==> a[k] == N + 1,
            forall |k:int| 0 <= k < N as int ==> b[k] == 1
    {
        a.set(i, b[i] + sum[0]);
        i = i + 1;
    }

    // Here, all elements of a will be N + 1 from the fourth loop
    proof {
        assert(forall |k:int| 0 <= k < N ==> a[k] == N + 1);
    }
}
}
// Score: (4, 2)
// Safe: True