
use vstd::prelude::*;
fn main() {}

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
            i < N as usize, // Fixed by AI
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
            i < a.len(),
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
            i < b.len(),
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
            i < b.len(),
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
            i < c.len(),
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
            i < c.len(),
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}

} // verus!


//             i < a.len(),
//   None: i < a.len()

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1
// Safe: True