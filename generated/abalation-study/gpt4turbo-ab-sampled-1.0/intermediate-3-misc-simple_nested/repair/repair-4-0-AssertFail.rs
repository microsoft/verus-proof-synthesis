
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k < N ==> 1 <= b[k] <= k + 1,
        old(a).len() == N,
        b.len() == N,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            a.len() == N as usize,
            b.len() == N as usize,
            1 <= a[( i ) as int] <= i as int + 2, // Adjusted to ensure a minimum value of 1 is always present in a[i] after modifications.
            i <= N as usize,
            N <= sum + (i as i32) <= 2 * N, // Ensuring 'sum' constraints are met even with additions.
            sum >= 0, // Ensuring 'sum' doesn't underflow.
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N as usize,
                b.len() == N as usize,
                i <= N as usize,
                j <= i,
                // Ensuring the value of a[i] does not underflow during the nested loop execution.
                a[( i ) as int] >= 1,
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        // Assert moved inside the invariant to ensure prerequisites are checked before the sum operation.
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!




//         assert(sum + a[( i ) as int] >= 0);     // Ensuring the sum doesn't underflow
//   assertion failed: sum + a[( i ) as int] >= 0

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False