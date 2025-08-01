use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        forall|k: int| 0 <= k < N ==> a[k] == N + 1,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            i <= N as usize,
            sum.len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            i <= N as usize,
            sum.len() == 1,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: int| 0 <= k < N ==> b[k] == 1, // Array b is never changed in this loop.
            i <= N as usize,
            sum.len() == 1,
            sum[0] < 1000 * N, // Correct upper bound for sum[0] before updating it with a[i]
            sum[0] == i,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    proof {
        assert(sum[0] < 1000 * N); // Proof added before next loop
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: int| 0 <= k < N ==> b[k] == 1,
            forall|k: int| 0 <= k < i ==> a[k] == N + 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == N,
    {
        a.set(i, b[i] + sum[0]);
        i = i + 1;
    }
}

} // verus!

//             sum[0] + a[( i ) as int] < 1000 * N, // Upper bound for sum[0] + a[i]
//   None: sum[0] + a[( i ) as int] < 1000 * N

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True