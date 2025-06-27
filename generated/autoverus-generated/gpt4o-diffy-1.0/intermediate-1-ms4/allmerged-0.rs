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
        sum[0] <= 3 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> a[j as int] == (j % 4) as i32,
            i <= N,
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
    {
        a.set(i, (i % 4) as i32);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|j: int| 0 <= j < N ==> a[j as int] == (j % 4) as i32,
            i <= N,
            if i == 0 {
                sum[0] == 0
            } else {
                sum[0] <= 3 * (i as i32)
            },
            forall|j: int|
                0 <= j < i ==> (if j == 0 {
                    sum[0] == 0
                } else {
                    sum[0] <= 3 * j && sum[0] == sum[0] + a[j as int]
                }),
            i <= N as usize,
            old(a).len() == N,
            old(sum).len() == 1,
            sum.len() == 1,
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


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2