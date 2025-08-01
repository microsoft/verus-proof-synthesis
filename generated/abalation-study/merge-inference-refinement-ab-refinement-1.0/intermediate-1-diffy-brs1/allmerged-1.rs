use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N > 0,
            0 <= N,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> (i % 1 == 0 ==> a[k] == 1) && (i % 1 != 0 ==> a[k] == 0),
            forall|k: int| 0 <= k < i as int ==> a[k] == 1 || a[k] == 0,
            forall|k: int| 0 <= k < i ==> a[k] == 1 || a[k] == 0,
            i <= N as usize,
            sum.len() == 1,
            old(sum).len() == 1,
    {
        if (i % 1 == 0) {
            a.set(i, 1);
        } else {
            a.set(i, 0);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            0 <= N,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> sum[0] == sum[0] + a[k],
            forall|k: int| 0 <= k < i as int ==> a[k] == 1 || a[k] == 0,
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= i as i32,
            sum[0] <= i,
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