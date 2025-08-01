
use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 4 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int|
                0 <= k < i ==> (if k % 4 == 0 {
                    a[k] == 4
                } else {
                    a[k] == 0
                }),
            forall|k: int|
                0 <= k < i ==> (k as usize % 4 == 0 ==> a[k as int] == 4) && (k as usize % 4 != 0
                    ==> a[k as int] == 0),
            i <= N as usize,
            old(a).len() == N,
            N < 1000, // Repeated invariant
            N > 0, // Repeated invariant
    {
        if (i % 4 == 0) {
            a.set(i, 4);
        } else {
            a.set(i, 0);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int|
                0 <= k < N ==> (if k % 4 == 0 {
                    a[k] == 4
                } else {
                    a[k] == 0
                }),
            forall|k: int| 1 <= k < i ==> sum[0] == sum[0] + a[k as int],
            i <= N as usize,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] <= 4 * i as i32,
            N < 1000, // Repeated invariant
            N > 0, // Repeated invariant
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
