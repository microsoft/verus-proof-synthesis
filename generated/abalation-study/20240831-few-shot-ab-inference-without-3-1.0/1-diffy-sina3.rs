
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        forall|k: int| 0 <= k < N ==> a[k] == N + 1,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i as int ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i as int ==> b[k] == 1,
            i <= N as usize,
            sum.len() == 1,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            // Updating this invariant because `a` is not modified in this loop
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i as int ==> a[k] == N + 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == N,
    {
        a.set(i, b[i] + sum[0]);
        i = i + 1;
    }
}

} // verus!
// Score: (0, 2)
// Safe: True