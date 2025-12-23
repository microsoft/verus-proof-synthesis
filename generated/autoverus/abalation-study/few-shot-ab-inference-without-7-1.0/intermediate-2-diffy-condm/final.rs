
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, N: u32)
    requires
        N > 0,
        old(a).len() == N,
    ensures
        forall|k: int| 0 <= k < N ==> a[k] % 2 == N % 2,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 0,
            i <= N as usize,
            N > 0,
    {
        a.set(i, 0);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < i ==> (a[k] % 2 == N % 2),
            i <= N as usize,
            N > 0,
    {
        if (N % 2 == 0) {
            a.set(i, a[i] + 2);
        } else {
            a.set(i, a[i] + 1);
        }
        i = i + 1;
    }
}

} // verus!
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3