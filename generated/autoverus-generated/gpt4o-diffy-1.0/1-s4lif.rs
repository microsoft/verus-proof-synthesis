
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
            a.len() == N,
            forall|j: int| 0 <= j < i as int ==> a[j] == 1,
            i <= N as usize,
            old(a).len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|j: int| 0 <= j < i as int ==> a[j] == 5,
            forall|j: int| i as int <= j < N ==> a[j] == 1,
            i <= N as usize,
            old(a).len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 4);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: int| 0 <= k < a.len() ==> a[k] == 5, // Updated because array 'a' is not modified in this loop
            i <= N as usize,
            old(a).len() == N,
            sum.len() == 1,
            sum[0] == 5 * i as i32,
            N > 0,
            N < 1000,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}

} // verus!

// Score: (4, 0)
// Safe: True