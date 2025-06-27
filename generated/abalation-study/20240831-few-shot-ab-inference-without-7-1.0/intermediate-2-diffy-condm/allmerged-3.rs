use vstd::prelude::*;
fn main() {}
verus! {

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
            a.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k] == 0,
            i <= N as usize,
    {
        a.set(i, 0);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            a.len() == N as usize,
            forall|k: int| 0 <= k < N ==> a[k] % 2 == 0,
            forall|k: int| 0 <= k < i ==> (a[k] % 2 == N % 2),
            forall|k: int|
                0 <= k < i ==> (if N % 2 == 0 {
                    a[k] == 2
                } else {
                    a[k] == 1
                }),
            forall|k: int| 0 <= k < i ==> a[k] % 2 == N % 2,
            forall|k: int|
                0 <= k < i ==> if N % 2 == 0 {
                    a[k] % 2 == 0
                } else {
                    a[k] % 2 == 1
                },
            i <= N as usize,
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


// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 5