
use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<u32>, N: u32) -> (sum: u32)
    requires
        old(a).len() == N,
        N <= 0x7FFF_FFFF,
    ensures
        sum <= 2 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: usize| 0 <= k < i ==> a[(k) as int] <= 2,
            i <= N as usize,
            N <= 0x7FFF_FFFF,
    {
        if (a[i] > 2) {
            a.set(i, 2);
        }
        i = i + 1;
    }
    i = 0;
    let mut sum: u32 = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|k: usize| 0 <= k < N as usize ==> a[(k) as int] <= 2,
            i <= N as usize,
            sum <= 2 * i as u32,
            N <= 0x7FFF_FFFF,
    {
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!

// Score: (3, 0)
// Safe: True