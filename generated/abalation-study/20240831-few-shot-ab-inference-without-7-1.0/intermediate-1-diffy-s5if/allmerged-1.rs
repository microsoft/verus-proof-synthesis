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
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j as int] == 5,
            forall|j: int| 0 <= j < i ==> a[j] == 5,
            i <= N as usize,
            sum.len() == 1,
    {
        a.set(i, 5);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            forall|j: int| 0 <= j < N ==> a[j as int] == 5,
            forall|j: int| 0 <= j < N ==> a[j] == 5,
            forall|j: int|
                0 <= j < i as int ==> if a[j as int] == 5 {
                    sum[0] == 5 * (j + 1) as i32
                } else {
                    true
                },
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 5 * N,
            sum[0] == 5 * i,
    {
        if (a[i] == 5) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 3