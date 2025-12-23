
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
            0 <= i <= N as usize,
            N < 1000,
            N > 0,
            a.len() == N,
            a.len() == N as usize,
            forall|j: int| 0 <= j < i as int ==> a[j as int] == (j % 5) as i32,
            forall|k: int| 0 <= k < i as int ==> a[k] == (k % 5) as i32,
            forall|j: int| 0 <= j < i ==> a[j as int] == ((j % 5) as i32),
            i <= N as usize,
            sum.len() == 1,
            N > 0,
            N < 1000, 
    {
        a.set(i, (i % 5) as i32);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            N < 1000,
            N > 0,
            a.len() == N,
            a.len() == N as usize,
            forall|j: int| 0 <= j < i as int ==> a[j as int] == (j % 5) as i32,
            forall|k: int| 0 <= k < N ==> a[k] == (k % 5) as i32,
            forall|j: int| 0 <= j < i ==> a[j as int] == ((j % 5) as i32),
            i <= N as usize,
            if i == 0 {
                sum[0] == 0
            } else {
                sum[0] <= 4 * i as i32
            },
            sum.len() == 1,
            sum[0] <= 4 * N,
            N > 0,
            N < 1000, 
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
