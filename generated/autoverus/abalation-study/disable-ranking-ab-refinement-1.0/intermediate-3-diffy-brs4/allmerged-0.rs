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
        sum[0] <= 4 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            forall|j: int|
                0 <= j < i ==> (if (j as usize % 4 == 0) {
                    a[j as int] == 4
                } else {
                    a[j as int] == 0
                }),
            forall|k: usize|
                0 <= k < i ==> (k % 4 == 0 ==> a[(k) as int] == 4) && (k % 4 != 0 ==> a[(k) as int]
                    == 0),
            i <= N as usize,
            sum.len() == 1,
    {
        if (i % 4 == 0) {
            a.set(i, 4);
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
            forall|j: int|
                0 <= j < N ==> (if (j as usize % 4 == 0) {
                    a[j as int] == 4
                } else {
                    a[j as int] == 0
                }),
            forall|k: usize|
                0 <= k < N as usize ==> (k % 4 == 0 ==> a[(k) as int] == 4) && (k % 4 != 0 ==> a[(
                k) as int] == 0),
            forall|k: usize| 0 <= k < i ==> sum[0] == sum@.index(0) + a[(k) as int],
            i <= N as usize,
            sum.len() == 1,
            sum[0] <= 4 * i as i32,
            sum[0] <= 4 * (i as i32),
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