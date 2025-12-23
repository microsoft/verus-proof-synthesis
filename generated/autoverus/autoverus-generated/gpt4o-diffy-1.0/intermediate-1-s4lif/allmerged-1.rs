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
            0 <= i <= N,
            a.len() == N,
            forall|j: int| 0 <= j < i as int ==> a[j] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N as usize,
            old(a).len() == N,
            forall|k: int| i <= k < N ==> a[k] <= 1,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            forall|j: int| 0 <= j < i as int ==> a[j] == 5,
            forall|j: int| i as int <= j < N ==> a[j] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 5,
            forall|k: int| i <= k < N ==> a[k] == 1,
            i <= N as usize,
            old(a).len() == N,
            forall|k: int| i <= k < N ==> a[k] <= 1,
            sum.len() == 1,
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
            0 <= i <= N,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 5,
            i <= N as usize,
            old(a).len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 5,
            forall|k: int| i <= k < N ==> a[k] == 5,
            sum.len() == 1,
            sum[0] == 5 * i as i32,
            sum[0] == i as i32 * 5,
            sum[0] == 5 * (i as i32),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 5