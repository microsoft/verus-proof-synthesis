
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
        sum[0] <= 5 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> (j % 5 == 0 ==> a[j] == 5) && (j % 5 != 0 ==> a[j] == 0),
            sum.len() == 1,
            N > 0,
            N < 1000,
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
            0 <= i <= N,
            a.len() == N,
            forall|j: int| 0 <= j < i ==> sum[0] == sum[0] + a[j],
            sum.len() == 1,
            sum[0] <= 5 * N,
            N > 0,
            N < 1000,
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
// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4