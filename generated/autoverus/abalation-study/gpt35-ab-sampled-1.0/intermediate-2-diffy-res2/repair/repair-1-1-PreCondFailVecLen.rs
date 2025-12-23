
use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, c: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
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
            i >= 0, // Array index not under bound
            i < a.len(), // Array access in bound
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
            i >= 0, // Array index not under bound
            i < a.len(), // Array access in bound
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
            i >= 0, // Array index not under bound
            i < b.len(), // Array access in bound
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
            i >= 0, // Array index not under bound
            i < b.len(), // Array access in bound
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
            i >= 0, // Array index not under bound
            i < c.len(), // Array access in bound
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
            i >= 0, // Array index not under bound
            i < c.len(), // Array access in bound
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

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False