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
            0 <= i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            forall |j: int| 0 <= j < i as int ==> a[j] == 2,
            forall |j: int| i as int <= j < a.len() ==> a[j] == old(a)[j],
    {
        a.set(i, 2);
        i = i + 1;
    }

    i = 0;

    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N,
            sum.len() == 1,
            forall |j: int| 0 <= j < N ==> a[j] == 2,
            forall |j: int| 0 <= j < sum.len() && j != i ==> sum[j] == 0,          
            sum[0] == 2 * i as i32,
    {
        if (a[i] == 2) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }

    proof {
        assert(2 * i as i32 == 2 * N);
    }
}
}
// Score: (2, 1)
// Safe: True