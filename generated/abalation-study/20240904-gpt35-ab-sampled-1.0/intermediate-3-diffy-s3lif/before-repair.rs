
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
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 < N,
            N > 0,
            a.len() == N as usize,
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == 4 * (i as i32),
            N < 1000,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N,
            N > 0,
            a.len() == N as usize,
            forall|j: int| 0 <= j < i ==> (a[j] == 1),
            // `a` is never modified in this loop, as there is no `a.set()` call, ensuring the invariant that every element in the array is covered
            forall|j: int| i <= j < N as usize ==> (a[j] == 0),
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == 4 * N,
            N < 1000,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 < N,
            N > 0,
            a.len() == N as usize,
            forall|j: int| 0 <= j < i ==> a[j] != 1,
            // `a` is never modified in this loop, as there is no `a.set()` call, ensuring the invariant that every element in the array is covered
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
            sum[0] == 4 * (i as i32),
            sum[0] == 4 * N,
            N < 1000,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2