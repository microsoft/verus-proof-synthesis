

use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 4 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    assert(sum[0] == 0);
    while (i < N as usize)
        invariant
            a.len() == N as usize,
            forall|k: usize| 0 <= k < i ==> a[(k) as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 0,
            N > 0,
            N < 1000,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N as usize,
            forall|k: usize| 0 <= k < i ==> a[(k) as int] == 4,
            forall|k: usize| i <= k < N as usize ==> a[(k) as int] == 1,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 0,
            N > 0,
            N < 1000,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 3);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N as usize,
            forall|k: usize| 0 <= k < i ==> a[(k) as int] == 4,
            (i == 0 || a[i as int - 1] == 4), // Removed the 1 condition since all elements should now be 4
            sum[0] <= 4 * (i as i32), // sum[0] can't exceed 4*N
            i <= N as usize,
            sum.len() == 1,
            N > 0,
            N < 1000,
    {
        sum.set(0, sum[0] + a[i]);
        if i > 0 {
            assert(a[i as int - 1] == 4); // Added this assertion
        }
        i = i + 1;
    }
} // verus!
}

//             a[( i ) as int] == 4, // Removed the 1 condition since all elements should now be 4
//   None: a[( i ) as int] == 4

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True