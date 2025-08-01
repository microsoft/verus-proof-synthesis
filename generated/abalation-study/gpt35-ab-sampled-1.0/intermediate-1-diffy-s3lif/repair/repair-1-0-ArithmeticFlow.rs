
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
    while (i < N as usize)
        invariant
            N < 1000,
            a.len() == N as usize,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 4 * old(a).len() as i32 - 4 * (N as i32 - i as i32),
            N > 0,
            old(a).len() == N,
            old(sum).len() == 1,
    {
        a.set(i, 1);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            a.len() == N as usize,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 4 * old(a).len() as i32 - 4 * (N as i32 - i as i32),
            N > 0,
            old(a).len() == N,
            old(sum).len() == 1,
            a[( i ) as int] >= 0, // Added by AI
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
            N < 1000,
            a.len() == N as usize,
            i <= N as usize,
            sum.len() == 1,
            sum[0] == 4 * old(a).len() as i32 - 4 * (N as i32 - i as i32),
            N > 0,
            old(a).len() == N,
            old(sum).len() == 1,
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}

} // verus!



//             a.set(i, a[i] - 1);
//   None: a[i] - 1

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True