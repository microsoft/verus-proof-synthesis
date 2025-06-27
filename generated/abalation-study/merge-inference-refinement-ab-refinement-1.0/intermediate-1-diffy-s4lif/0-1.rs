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
        sum[0] == 5 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
        invariant
            i <= N as usize,
            0 < N < 1000,
            a.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < i ==> a[k] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            a.len() == N,
            0 < N < 1000,
            forall |k:int| 0 <= k < i ==> a[k] == 5,
            forall |k:int| i <= k < N ==> a[k] == 1,
    case a[i] == 1:
        {
            a.set(i, a[i] + 4);
            i = i + 1;
        }
    else:
        {
            a.set(i, a[i] - 1);
            i = i + 1;
        }

    i = 0;
    while (i < N as usize)
        invariant
            i <= N as usize,
            0 < N < 1000,
            a.len() == N,
            sum.len() == 1,
            forall |k:int| 0 <= k < i ==> sum[0] == 5 * k,
            forall |j:int| 0 <= j < i ==> a[j] == 5,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1