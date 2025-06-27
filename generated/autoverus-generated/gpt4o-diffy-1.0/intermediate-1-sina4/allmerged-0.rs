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
        forall|k: int| 0 <= k < N ==> b[k] == N + 2,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            0 <= N < 1000,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            0 <= N < 1000,
            a.len() == N,
            b.len() == N,
            forall|j: int|
                0 <= j < N as int ==> a[j] == if j < i as int {
                    1
                } else {
                    a[j]
                },
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            0 <= N < 1000,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < i ==> a[j] == N as i32 + 1,
            forall|j: int| i <= j < N as int ==> a[j] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == N + 1,
            forall|k: int| i <= k < N ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == N,
    {
        a.set(i, a[i] + sum[0]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            0 <= N < 1000,
            a.len() == N,
            b.len() == N,
            forall|j: int| 0 <= j < N as int ==> a[j] == N as i32 + 1,
            forall|j: int| 0 <= j < i ==> b[j] == N + 2,
            forall|j: int| i <= j < N as int ==> b[j] == b[j],
            forall|k: int| 0 <= k < N ==> a[k] == N + 1,
            forall|k: int| 0 <= k < i ==> b[k] == N + 2,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == N,
    {
        b.set(i, a[i] + 1);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 4, Errors: 1, Verus Errors: 4