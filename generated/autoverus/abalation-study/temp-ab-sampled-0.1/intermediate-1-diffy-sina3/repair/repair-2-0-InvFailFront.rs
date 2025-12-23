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
            a.len() == N,
            b.len() == N,
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
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> b[k] == 1,
            i <= N as usize,
            sum.len() == 1,
    {
        b.set(i, 1);
        i = i + 1;
    }
    i = 0;
    proof {
        assert(forall|k: int| 0 <= k < N ==> a[k] == 1);
    } // Added by AI
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < N ==> a[k] == 1, // a is not modified in this loop
            forall|k: int| 0 <= k < N ==> b[k] == 1, // b is not modified in this loop
            i <= N as usize,
            sum.len() == 1,
            sum[0] == i as i32,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == N + 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == N,
            b[( i ) as int] >= 0, // Added by AI
            b[( i ) as int] <= 1, // Added by AI
            sum[0] >= 0, // Added by AI
            sum[0] <= N, // Added by AI
    {
        a.set(i, b[i] + sum[0]);
        i = i + 1;
    }
}

} // verus!

//             forall|k: int| 0 <= k < N ==> a[k] == 1, // a is not modified in this loop
//   None: forall|k: int| 0 <= k < N ==> a[k] == 1

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True