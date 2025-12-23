
use vstd::prelude::*;
fn main() {}

verus! {
pub fn myfun(a: &mut Vec<usize>, N: usize)
    requires
        N < 100,
        old(a).len() == N,
    ensures
        forall |k: int| 0 <= k < N ==> a[k] == 2,
{
    let mut i: usize = 0;

    while (i < N)
        invariant 
            i <= N,
            a.len() == N,
            (forall |k: int| 0 <= k < i ==> a[k] == 0),
        {
            a.set(i, 0);
            i = i + 1;
        }

    i = 0;
    while (i < N)
        invariant
            i <= N,
            a.len() == N,
            (forall |k: int| 0 <= k < i ==> a[k] == 2),
            (forall |k: int| i <= k < N ==> a[k] == 0),
        {
            a.set(i, a[i] + 2);
            i = i + 1;
        }
}
}

// is safe: False
// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0