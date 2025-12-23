

use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, N: u32)
    requires
        N > 0,
        old(a).len() == N,
    ensures
        forall |k:i32| 0 <= k < N as i32 ==> a[( k ) as int] % 2 == N % 2,
{
    let mut i: usize = 0;

    while (i < N as usize)
        invariant
            N > 0,
            i <= N as usize,
            a.len() == N as usize,
            forall |k:i32| 0 <= k < i as i32 ==> a[( k ) as int] == 0,
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
            forall |k:i32| 0 <= k < i as i32 ==> a[( k ) as int] % 2 == N % 2,
            forall |k:i32| i as i32 <= k < N as i32 ==> a[( k ) as int] == 0,
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
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 5