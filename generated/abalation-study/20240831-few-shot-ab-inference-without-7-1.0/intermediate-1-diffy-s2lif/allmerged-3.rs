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
        sum[0] == 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            a.len() == N as usize,
            forall|j: int| 0 <= j < i ==> a[j as int] == 1,
            forall|j: int| 0 <= j < i as int ==> a[j as int] == 1,
            i <= N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            a.len() == N as usize,
            forall|j: int| 0 <= j < N ==> old(a)[j] == 1,
            forall|j: int| 0 <= j < i ==> a[j as int] == 3,
            forall|j: int| 0 <= j < i as int ==> a[j as int] == 3,
            forall|j: int| i as int <= j < N ==> a[j as int] == 1,
            i <= N,
            forall|j: int| 0 <= j < i ==> a[j] == 3,
            i <= N as usize,
            old(a).len() == N,
            sum.len() == 1,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 2);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            a.len() == N as usize,
            forall|j: int| 0 <= j < N ==> a[j as int] == 3,
            forall|j: int| 0 <= j < i as int ==> a[j as int] == 3,
            i <= N,
            forall|j: int| 0 <= j < N ==> a[j] == 3,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * N,
            sum[0] <= 3 * i,
            sum[0] == (i as int) * 3,
            sum[0] == 3 * i,
            sum[0] == 3 * i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 5