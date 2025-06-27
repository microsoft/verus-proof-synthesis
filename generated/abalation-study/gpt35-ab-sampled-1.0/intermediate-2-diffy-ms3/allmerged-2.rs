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
            0 <= i <= N as usize,
            N < 1000,
            N > 0,
            a.len() == N as usize,
            forall|j: int| 0 <= j < i ==> a[j] == (j % 3) as i32,
            i <= N as usize,
            sum.len() == 1,
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            N < 1000,
            N > 0,
            a.len() == N as usize,
            forall|j: int| 0 <= j < i ==> a[j] == (j % 3) as i32,
            forall|j: int| 1 <= j < i ==> sum[j] == a[j - 1],
            i <= N as usize,
            old(sum).len() == 1,
            old(sum)[0] + a[(i) as int] <= 2 * (i + 1),
            sum.len() == 1,
            sum[0] <= 2 * N,
            sum[0] <= 2 * i as i32,
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


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 8