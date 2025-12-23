use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

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
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k as int] == (k % 3) as i32,
            forall|k: int| 0 <= k < i ==> a[k] == (k % 3) as i32,
            i <= N as usize,
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
            forall|k: int| 0 <= k < N ==> a[k] == (k % 3) as i32,
            forall|k: int| 0 <= k < i ==> a[k as int] == (k % 3) as i32,
            i <= N as usize,
            if i == 0 {
                sum[0] == 0
            } else {
                sum[0] <= 2 * i as i32
            },
            if i > 0 {
                sum[0] <= 2 * i as i32
            } else {
                true
            },
            i > 0 ==> sum[0] <= 2 * N,
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

// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1