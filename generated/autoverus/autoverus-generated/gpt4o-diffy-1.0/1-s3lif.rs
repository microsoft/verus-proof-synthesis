use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 < N < 1000,
            a.len() == N,
            forall|k: int| 0 <= k < i as int ==> a[k] == 1,
            i <= N as usize,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            forall|k: int| i <= k < N ==> a[k] == old(a)[k],
            i <= N,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N < 1000,
            a.len() == N,
            forall|k: int| 0 <= k < i as int ==> a[k] == 4,
            forall|k: int| i as int <= k < N ==> a[k] == 1,
            i <= N as usize,
            forall|k: int| 0 <= k < i ==> a[k] == 4,
            i <= N,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N < 1000,
            forall|k: int| 0 <= k < i as int ==> a[k] == 4,
            forall|k: int| i as int <= k < N ==> a[k] == 4,
            i <= N as usize,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 4,
            forall|k: int| i <= k < N ==> a[k] == 4,
            i <= N,
            sum.len() == 1,
            sum[0] == 4 * (i as i32),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}

} // verus!



// Score: (4, 0)
// Safe: True