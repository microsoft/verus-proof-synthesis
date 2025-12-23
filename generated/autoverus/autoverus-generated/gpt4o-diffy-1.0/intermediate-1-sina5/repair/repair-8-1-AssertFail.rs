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
        forall|k: int| 0 <= k < N ==> a[k] == 2 * N + 1,
{
    let mut i: usize = 0;
    sum.set(0, 0);
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 1,
            sum.len() == 1,
            sum[0] == 0,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            sum.len() == 1,
            sum[0] == 0,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    proof {
        assert(forall|k: int| 0 <= k < N ==> a[k] == 1); // Added by AI
    }
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            forall|k: int| 0 <= k < N ==> b[k] == 1,
            sum.len() == 1,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 1,
            forall|k: int| 0 <= k < N ==> b[k] == 1,
            sum.len() == 1,
            sum[0] == N + i as i32,
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            N > 0,
            N < 1000,
            a.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == 2 * N + 1,
            sum.len() == 1,
            sum[0] == 2 * N,
            a[(i) as int] <= 1, // Ensure a[i] is not greater than 1 before update
            a[(i) as int] + sum[0] <= 2 * N + (2 * N), // Upper bound condition,
            a[(i) as int] + sum[0] >= i32::MIN, // Lower bound condition to prevent underflow
    {
        a.set(i, a[i] + sum[0]);
        proof {
            assert(i > 0 ==> a[(i - 1) as int] + sum[0] <= 4 * N); // Added by AI
        }
        i = i + 1;
    }
}

}

//             assert(a[(i - 1) as int] + sum[0] <= 4 * N); // Added by AI
//   assertion failed: a[(i - 1) as int] + sum[0] <= 4 * N

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True