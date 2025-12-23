
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
            0 <= i <= N as usize,
            a.len() == N,
            forall|j: int|
                0 <= j < i ==> if j % 5 == 0 {
                    a[j as int] == 5
                } else {
                    a[j as int] == 0
                },
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
            0 <= i <= N as usize,
            forall|j: int| 0 <= j < a.len() ==> if j == 0 { sum[0] == 0 } else { sum[0] == sum[0] + a[j as int] },  // Comment: Updated invariant to cover every element in the array, as a[j] is never set in this loop
            sum.len() == 1,
            a.len() == N,
            sum[0] <= 5 * i,
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
