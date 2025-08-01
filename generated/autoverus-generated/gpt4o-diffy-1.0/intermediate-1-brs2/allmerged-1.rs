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
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> (a[k] == 2 && k % 2 == 0) || (a[k] == 0 && k % 2 != 0),
            forall|k: int|
                0 <= k < i ==> if k % 2 == 0 {
                    a[k as int] == 2
                } else {
                    a[k as int] == 0
                },
            i <= N as usize,
            sum.len() == 1,
    {
        if (i % 2 == 0) {
            a.set(i, 2);
        } else {
            a.set(i, 0);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|k: int| 0 <= k < N ==> (a[k] == 2 && k % 2 == 0) || (a[k] == 0 && k % 2 != 0),
            forall|k: int|
                0 <= k < N ==> if k % 2 == 0 {
                    a[k as int] == 2
                } else {
                    a[k as int] == 0
                },
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 2 * (i as i32),
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


// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2