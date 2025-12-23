use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, N: u32)
    requires
        N > 0,
        old(a).len() == N,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] % 2 == N % 2,
{
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            forall |j:int| 0 <= j < i ==> a[j] == 0,
    {
        a.set(i, 0);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 < N,
            i <= N as usize,
            a.len() == N,
            forall |j:int| 0 <= j < i ==> a[j] % 2 == N % 2,
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
// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 3