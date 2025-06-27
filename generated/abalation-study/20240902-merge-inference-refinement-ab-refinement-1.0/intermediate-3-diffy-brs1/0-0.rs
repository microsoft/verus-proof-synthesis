use vstd::prelude::*;
fn main() {}
verus!{
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
            i <= N as usize,
            a.len() == N,
            N > 0,
            forall |j: int| 0 <= j < i ==> ((j % 2 == 0 && a[j] == 1) || (j % 2 != 0 && a[j] == 0)),
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
            i <= N as usize,
            sum.len() == 1,
            a.len() == N,
            N > 0,
            forall |j: int| 0 <= j < i ==> ((j % 2 == 0 && a[j] == 1) || (j % 2 != 0 && a[j] == 0)),
            sum[0] <= i as i32,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 5