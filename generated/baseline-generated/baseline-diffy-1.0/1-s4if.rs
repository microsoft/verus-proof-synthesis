use vstd::prelude::*;
fn main() {}
verus! {
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;

    while i < N as usize
        invariant
            i <= (N as usize),
            a@.len() == N as int,
            forall |k:int| 0 <= k < i as int ==> a[k] == 4,
    {
        a.set(i, 4);
        i = i + 1;
    }
    
    i = 0;
    while i < N as usize
        invariant
            i <= (N as usize),
            a@.len() == N as int,
            forall |k:int| 0 <= k < N as int ==> a[k] == 4,
            sum@.len() == 1,
            sum[0] == 4 * (i as i32), // Sum is 4 multiplied by the number of elements processed so far
    {
        if a[i] == 4 {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
    assert(sum[0] == 4 * N);
}
}
// Score: (2, 2)
// Safe: False