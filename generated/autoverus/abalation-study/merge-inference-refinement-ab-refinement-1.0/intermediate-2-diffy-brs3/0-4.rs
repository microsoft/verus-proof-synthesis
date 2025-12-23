use vstd::prelude::*;
fn main() {}
verus!{

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
            0 <= N < 1000, 
            i <= N as usize,
            a.len() == N,
            forall |k: int| 0 <= k < i ==> (if k % 3 == 0 { a[k] == 3 } else { a[k] == 0 }),
            forall |k: int| i <= k < N as usize ==> old(a@[k]) == a[k], // initially a is unchanged from old
    {
        if (i % 3 == 0) {
            a.set(i, 3);
        } else {
            a.set(i, 0);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= N < 1000,
            sum.len() == 1,
            a.len() == N,
            i <= N as usize,
            i == 0 ==> sum[0] == 0,
            i > 0 ==> sum[0] == a.subrange(0, i as int).iter().sum(),
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1