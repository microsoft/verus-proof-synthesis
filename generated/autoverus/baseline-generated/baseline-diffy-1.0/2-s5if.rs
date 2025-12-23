use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 5 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while i < N as usize
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            sum@.len() == 1,
            forall |j: int| 0 <= j < i as int ==> a[j] == 5,
            forall |j: int| i as int <= j < N as int ==> old(a)@.index(j as int) == a[j],
    {
        a.set(i, 5);
        i = i + 1;
    }

    i = 0;
    while i < N as usize
        invariant
            0 <= i <= N as usize,
            a@.len() == N,
            sum@.len() == 1,
            sum[0] <= 5 * (i as i32),  // Sum should not exceed 5 * i
            sum[0] == 5 * i as i32, // Sum should be multiples of 5 
            forall |j: int| 0 <= j < N as int ==> a[j] == 5,   // All elements in 'a' are set to 5
    {
        if a[i] == 5 {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}
}
// Score: (2, 2)
// Safe: False