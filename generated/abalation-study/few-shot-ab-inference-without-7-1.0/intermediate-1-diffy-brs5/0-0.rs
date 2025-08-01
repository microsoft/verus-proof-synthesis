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
        sum[0] <= 5 * N,
{
    let mut i: usize = 0;
    
    while (i < N as usize)
        invariant
            i <= N,
            N > 0,
            N < 1000,
            a.len() == N,
            forall |j: int| 0 <= j < i ==> (if j % 5 == 0 { a[j as int] == 5 } else { a[j as int] == 0 }),
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
            i <= N,
            N > 0,
            N < 1000,
            a.len() == N,
            sum.len() == 1,
            forall |j: int| 0 <= j < N ==> (if j % 5 == 0 { a[j as int] == 5 } else { a[j as int] == 0 }),
            forall |j: int| 0 <= j < i ==> sum[0] <= 5 * j,
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }

    assert(sum[0] <= 5 * N);
}
}




// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1