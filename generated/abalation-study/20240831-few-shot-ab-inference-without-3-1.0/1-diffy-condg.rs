use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        forall|k: int| 0 <= k < N ==> a[k] == 0,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i as int ==> a[k] == 1,
            forall|k: int| i as int <= k < N ==> a[k] == old(a)[k],
            i <= N as usize,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == (i as i32),
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|k: int| sum[0] != N ==> (0 <= k < i as int ==> a[k] == 2),
            forall|k: int| sum[0] == N ==> (0 <= k < i as int ==> a[k] == 0),
            forall|k: int| 0 <= k < i as int ==> a[k] == 0,
            forall|k: int| i as int <= k < N ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] != -1,
            sum[0] == N,
    {
        if (sum[0] == N) {
            a.set(i, a[i] - 1);
        } else {
            a.set(i, a[i] + 1);
        }
        i = i + 1;
    }
    assert(sum[0] == N);
    assert(forall|k: int| 0 <= k < N ==> a[k] == 0);
}

} // verus!


// Score: (4, 0)
// Safe: True