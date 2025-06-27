
use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Seq<i32>, b: &mut Seq<i32>, c: &mut Seq<i32>, sum: &mut Seq<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(c).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] <= 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            i <= N as usize,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
            i <= N as usize,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
            i >= 0,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            b.len() == N,
            i <= N as usize,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
            i >= 0,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            b.len() == N,
            i <= N as usize,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
            i >= 0,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            c.len() == N,
            i <= N as usize,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
            i >= 0,
    {
        c.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            c.len() == N,
            i <= N as usize,
            sum[0] <= 3 * N,
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(c).len() == N,
            old(sum).len() == 1,
            N < 1000,
            i >= 0,
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}

} // verus!


//         sum.set(0, sum[0] + c[i]);
// failed precondition
//         i < vec.view().len(),
//   failed precondition: i < vec.view().len()
//   None: sum[0]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 14
// Safe: False