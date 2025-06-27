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
        sum[0] == 6 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);
    while (i < N as usize)
        invariant
            0 <= N,
            0 <= i as i32 <= N,
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            forall|k: int| 0 <= k < i as int ==> a[k as int] == 1,
            forall|k: int| i as int <= k < N as int ==> a[k as int] == old(a)[k as int],
            i <= N as usize,
            old(a).len() == N,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= N,
            0 <= i as i32 <= N,
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 6,
            forall|k: int| 0 <= k < i as int ==> a[k as int] == 6,
            forall|k: int| i <= k < N ==> a[k] == 1,
            forall|k: int| i as int <= k < N as int ==> a[k as int] == 1,
            i <= N as usize,
            old(a).len() == N,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 5);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= N,
            0 <= i as i32 <= N,
            N < 1000,
            N > 0,
            forall|k: int| 0 <= k < sum.len() as int ==> old(sum)[k as int] == 0,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 6 * (i as i32),
            sum[0] == 6 * i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 5