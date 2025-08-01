use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);
    while (i < N as usize)
        invariant
            a.len() == N,
            b.len() == N,
            0 <= i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|j: int| 0 <= j < i ==> a[j as int] == 1,
            forall|j: int| 0 <= j < i as int ==> a[j] == 1,
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
            b.len() == N,
            0 <= i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|j: int| 0 <= j < i ==> b[j as int] == 1,
            forall|j: int| 0 <= j < i as int ==> b[j] == 1,
            i <= N as usize,
            sum.len() == 1,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < N ==> a[j as int] == 1,
            forall|j: int| 0 <= j < N ==> a[j] == 1,
            i <= N as usize,
            0 <= i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|j: int| 0 <= j < N as usize ==> a[j] == 1,
            sum.len() == 1,
            sum[0] <= i as i32,
            sum[0] >= 0,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < N ==> a[j as int] == 1,
            forall|j: int| 0 <= j < N ==> b[j as int] == 1,
            forall|j: int| 0 <= j < N ==> b[j] == 1,
            i <= N as usize,
            0 <= i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|j: int| 0 <= j < N as usize ==> b[j] == 1,
            sum.len() == 1,
            sum[0] <= N + i as i32,
            sum[0] >= 0,
            sum[0] <= (N + i) as i32,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 4, Errors: 1, Verus Errors: 3