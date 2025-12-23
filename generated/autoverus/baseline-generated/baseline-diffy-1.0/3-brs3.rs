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
            0 <= i <= N as usize,
            a@.len() as int == N,
            forall |j: int| 0 <= j < i ==> if j % 3 == 0 { a[j] == 3 } else { a[j] == 0 },
            forall |j: int| i <= j < a.len() ==> a[j] == old(a)[j],
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
            0 <= i <= N as usize,
            a@.len() as int == N,
            sum@.len() == 1,
            forall |j: int| 0 <= j < a.len() ==> if j % 3 == 0 { a[j] == 3 } else { a[j] == 0 },
            sum[0] <= 3 * i as i32,
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
// Score: (1, 2)
// Safe: True