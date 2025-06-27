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
            N < 1000,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j as int] == 2,
            i <= N as usize,
            sum.len() == 1,
    {
        a.set(i, 2);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            forall|j: int| 0 <= j < i ==> a[j as int] == 2,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 2 * N,
            sum[0] >= 0,
    {
        if (a[i] == 2) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 7