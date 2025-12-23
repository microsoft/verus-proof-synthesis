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
        sum[0] <= 5 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N as usize,
            forall|k: int|
                0 <= k < i as int ==> (k % 5 == 0 ==> a[k as int] == 5) && (k % 5 != 0
                    ==> a[k as int] == 0),
            i <= N as usize,
            sum.len() == 1,
    {
        if (i % 5 == 0) {
            a.set(i, 5);
        } else {
            a.set(i, 0);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N as usize,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 5 * i as i32,
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


// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 3