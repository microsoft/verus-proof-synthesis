use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> (a[k as int] == 1 || a[k as int] == 0),
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            forall|k: int| i <= k < N ==> a[k] == old(a)[k],
            i <= N as usize,
            sum.len() == 1,
    {
        if (i % 1 == 0) {
            a.set(i, 1);
        } else {
            a.set(i, 0);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            (if i == 0 {
                sum[0] == 0
            } else {
                sum[0] <= i && sum[0] == sum[0]
            }),
            0 <= i <= N,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            forall|k: int| 0 <= k < i ==> a[k as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= N,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}

} // verus!


// Score: (2, 2)
// Safe: True