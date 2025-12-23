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
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N as usize > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == (k % 3) as i32,
            forall|j: int| 0 <= j < i ==> a[j] == (j % 3) as i32,
            i <= N,
            sum.len() == 1,
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            a[(i) as int] <= 2,
            i <= N,
            forall|j: int| 0 <= j < i ==> a[j] == (j % 3) as i32,
            if i == 0 {
                sum[0] == 0
            } else {
                sum[0] == sum[0] + a[i - 1]
            },
            sum.len() == 1,
            sum[0] <= 2 * (N - (i as i32)),
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


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 7