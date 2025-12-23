
use vstd::prelude::*;

verus! {
pub fn myfun(a: &mut Vec<i32>, N: u32)
    requires
        N > 0,
        old(a).len() == N,
    ensures
        forall |k: int| 0 <= k < N ==> a[k] % 2 == N % 2,
{
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            N > 0,
            i <= N as usize,
            a.len() == N as usize,
            forall |k: int| 0 <= k < i ==> a[k] == 0,
    {
        a.set(i, 0);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            i <= N as usize,
            a.len() == N as usize,
            forall |k: int| 0 <= k < N ==> a[k] == 0,
            if (N % 2 == 0) {
                forall |k: int| 0 <= k < i ==> a[k] % 2 == 0
            } else {
                forall |k: int| 0 <= k < i ==> a[k] % 2 == 1
            },
    {
        if (N % 2 == 0) {
            a.set(i, a[i] + 2);
        } else {
            a.set(i, a[i] + 1);
        }
        i = i + 1;
    }
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1