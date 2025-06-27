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
            0 <= N < 1000,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k as int] == (k % 4) as i32,
            forall|k: int| 0 <= k < i ==> a[k] == (k % 4) as i32,
            i <= N as usize,
    {
        a.set(i, (i % 4) as i32);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            forall|k: int| 0 <= k < N ==> a[k as int] == (k % 4) as i32,
            0 <= N < 1000,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> sum[0] == sum[0] + a[k] - a[k],
            i <= N as usize,
            if i == 0 {
                sum[0] == old(sum)[0]
            } else {
                i > 0 ==> sum[0] <= (i as i32 - 1) * 3
            },
            sum.len() == 1,
            sum[0] <= 3 * (i as i32),
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


// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 1