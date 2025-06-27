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
        sum[0] <= 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    
    while i < N as usize
    invariant
        0 <= i <= N as usize,
        a@.len() == N,
        forall |k: int| 0 <= k < i ==> a[k] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;

    while i < N as usize
    invariant
        0 <= i <= N as usize,
        sum@.len() == 1,
        a@.len() == N,
        forall |k: int| 0 <= k < a.len() ==> a.len() > k && a[k] == 1,
        sum[0] + (N - i as i32) <= N,
    {
        sum.set(0, sum[0] + a[i]);
        proof {
            assert(sum[0] + (N - (i as i32 + 1)) <= N);
        }
        i = i + 1;
    }

    i = 0;

    while i < N as usize
    invariant
        0 <= i <= N as usize,
        b@.len() == N,
        forall |k: int| 0 <= k < i ==> b[k] == 1,
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;

    while i < N as usize
    invariant
        0 <= i <= N as usize,
        sum@.len() == 1,
        b@.len() == N,
        forall |k: int| 0 <= k < b.len() ==> b.len() > k && b[k] == 1,
        sum[0] + (N - i as i32) <= 2 * N,
    {
        sum.set(0, sum[0] + b[i]);
        proof {
            assert(sum[0] + (N - (i as i32 + 1)) <= 2 * N);
        }
        i = i + 1;
    }
}
}

// Score: (4, 1)
// Safe: False