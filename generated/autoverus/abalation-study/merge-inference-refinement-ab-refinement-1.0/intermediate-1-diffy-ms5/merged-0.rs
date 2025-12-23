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
        sum[0] <= 4 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == (k % 5) as i32,
            forall|k: int| 0 <= k < i ==> a[k] == (k as i32 % 5),
            i <= N as usize,
    {
        a.set(i, (i % 5) as i32);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            forall|k: int| 0 <= k < N ==> a[k] == (k % 5) as i32,
            a.len() == N,
            forall|k: int| 0 < k < i ==> sum[0] == sum[0] + a[k],
            forall|k: int| 0 <= k < N ==> a[k] == (k as i32 % 5),
            i <= N as usize,
            if i == 0 {
                true
            } else {
                sum[0] <= 4 * (i as i32)
            },
            i == 0 ==> sum[0] == 0,
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