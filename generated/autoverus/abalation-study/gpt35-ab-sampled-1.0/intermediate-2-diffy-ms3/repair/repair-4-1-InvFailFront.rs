
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
        N < 1000,
    ensures
        sum[0] <= 2 * N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N as usize,
            i <= N as usize,
    {
        a.set(i, (i % 3) as i32);
        i = i + 1;
    }
    i = 0;
    while (i < N as usize)
        invariant
            N < 1000,
            N > 0,
            a.len() == N as usize,
            i <= N as usize,
            old(sum)[0] + a[(i) as int] <= 2 * (i + 1),
            sum.len() == 1,
            0 <= i, // Added by AI
            i < N as usize, // Added by AI
            a[( i ) as int] >= 0, // Added by AI
            a[( i ) as int] <= 2, // Added by AI
            sum[0] + a[( i ) as int] >= 0, // Added by AI
            sum[0] + a[( i ) as int] <= 2 * (i + 1), // Added by AI
        {
            if (i == 0) {
                sum.set(0, 0);
            } else {
                sum.set(0, sum[0] + a[i]);
            }
            i = i + 1;
            assert(old(sum)[0] + a[i as int] <= 2 * (i + 1)); // Added by AI
        }
    }
}

} // verus!


//             old(sum)[0] + a[(i) as int] <= 2 * (i + 1),
//   None: old(sum)[0] + a[(i) as int] <= 2 * (i + 1)

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False