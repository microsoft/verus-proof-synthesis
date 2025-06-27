
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k <= # [trigger] b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    assert(sum >= N); // Added by AI
    while (i < N as usize)
        invariant
            N <= 0x3FFF_FFFF,
            b.len() == N,
            forall|k: int| k <= # [trigger] b[k] <= k + 1,
            i <= N as usize,
            old(a).len() == N,
            sum <= 2 * N,
            sum >= N,
            a.len() == N, 
            i >= 0,
            a[( i ) as int] >= i as i32, // Added by AI, ensuring a[i] is greater than or equal to i
            a[( i ) as int] <= N, // Added by AI using N as the upper bound for a[i]
            sum + a[( i ) as int] >= sum, // Added by AI, ensuring no arithmetic overflow
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                j <= i,
                a.len() == N,
                j >= 0,
                a[( i ) as int] >= i as i32, // Added by AI, ensuring a[i] is greater than or equal to i
                a[( i ) as int] <= N, // Added by AI using N as the upper bound for a[i]
                sum + a[( i ) as int] >= sum, // Added by AI, ensuring no arithmetic overflow
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!


//             sum >= N,
//   None: sum >= N

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 4
// Safe: True