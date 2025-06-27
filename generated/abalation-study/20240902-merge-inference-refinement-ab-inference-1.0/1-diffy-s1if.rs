use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        sum[0] == N,
{
    let mut i: usize = 0;
    sum.set(0, 0);
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            forall|k: int| i <= k < N as usize ==> a[k] == old(a)[k],
            forall|k: int| i <= k < N ==> old(a)[k] == a[k],
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
            forall|k: int| 0 <= k < N as usize ==> a[k] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= i,
            sum[0] >= 0,
            sum[0] == i as i32,
    {
        if (a[i] == 1) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}

} // verus!


// Score: (3, 0)
// Safe: True