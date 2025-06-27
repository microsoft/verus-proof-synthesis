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
    let mut i: usize = 0;
    sum.set(0, 0);
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            a.len() == N as usize,
            forall|j: int| 0 <= j < i ==> a[j] == 3,
            forall|j: usize| 0 <= j < i ==> a[(j) as int] == 3,
            forall|j: usize| i <= j < a.len() ==> old(a)[(j) as int] == a[(j) as int],
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 0,
    {
        a.set(i, 3);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            a.len() == N as usize,
            forall|j: int| 0 <= j < N ==> a[j] == 3,
            forall|j: usize| 0 <= j < N as usize ==> a[(j) as int] == 3,
            forall|j: usize| 0 <= j < i ==> a[(j) as int] == 3,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 3 * i,
            sum[0] == 3 * i,
            sum[0] == 3 * i as i32,
    {
        if (a[i] == 3) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 3