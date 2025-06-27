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
        sum[0] == 5 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i as int ==> a[k] == 5,
            i <= N as usize,
            sum.len() == 1,
    {
        a.set(i, 5);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 5,
            forall|k: int| 0 <= k < i as int ==> a[k] == 5,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 5 * i as i32,
            sum[0] == 5 * i as i32,
    {
        if (a[i] == 5) {
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