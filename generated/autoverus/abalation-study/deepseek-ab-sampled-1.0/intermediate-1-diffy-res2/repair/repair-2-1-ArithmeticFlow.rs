

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
            0 <= N,
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            forall|j: usize| j < i ==> a[(j) as int] == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            N < 1000,
            a.len() == N,
            b.len() == N,
            forall|j: usize| j < i ==> a[(j) as int] == 1,
            i <= N,
            sum[0] == i as i32,
            sum[0] == 0 + i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            N < 1000,
            b.len() == N,
            b.len() == N,
            forall|j: usize| j < i ==> b[(j) as int] == 1,
            sum[0] + b[( i ) as int] <= 2 * N + i as i32, // Added by AI
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            N < 1000,
            b.len() == N,
            b.len() == N,
            forall|j: usize| j < i ==> b[(j) as int] == 1,
            sum[0] + b[( i ) as int] <= 2 * N as i32, // Added by AI
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            N < 1000,
            c.len() == N,
            b.len() == N,
            forall|j: usize| j < i ==> c[(j) as int] == 1,
            sum[0] + b[( i ) as int] <= 2 * N + i as i32, // Added by AI
    {
        c.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            N < 1000,
            c.len() == N,
            b.len() == N,
            forall|j: usize| j < i ==> c[(j) as int] == 1,
            sum[0] + b[( i ) as int] <= 2 * N as i32, // Added by AI
    {
        sum.set(0, sum[0] + c[i]);
        i = i + 1;
    }
}

} // verus!





//         sum.set(0, sum[0] + b[i]);
//   None: sum[0] + b[i]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True