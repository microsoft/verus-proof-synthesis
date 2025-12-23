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
        sum[0] == 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            forall|j: int| 0 <= j < i as int ==> a[j as int] == 1,
            i <= N,
            i <= N as usize,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 2 || a[j] == 0,
            forall|j: int| 0 <= j < i as int ==> a[j as int] == 2,
            forall|j: int| 0 <= j < i ==> a[j] == 2,
            i <= N,
            i <= N as usize,
            sum.len() == 1,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 1);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 2 || a[j] == 0,
            forall|j: int| 0 <= j < i as int ==> a[j as int] == 2,
            forall|j: int| 0 <= j < i ==> a[j] == 2,
            i <= N,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 2 * (i as i32),
            sum[0] == i as i32 * 2,
            sum[0] == 2 * i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 9