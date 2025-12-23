use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            0 < N < 1000,
            sum.len() == 1,
            forall |j:int| 0 <= j < i ==> a[j] == 2,
    {
        a.set(i, 2);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            0 < N < 1000,
            sum.len() == 1,
            forall |j:int| 0 <= j < N ==> a[j] == 2, //maintains the condition of initialization
            sum[0] == 2 * i,
    {
        if (a[i] == 2) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}
}
// Score: (3, 0)
// Safe: True