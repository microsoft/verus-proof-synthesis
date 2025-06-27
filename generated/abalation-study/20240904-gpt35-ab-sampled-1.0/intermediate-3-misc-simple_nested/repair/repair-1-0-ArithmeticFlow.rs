
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| k <= #[trigger] b[k] <= k + 1,
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
            N <= 0x3FFF_FFFF,
            a.len() == N,
            b.len() == N,
            forall|k: int| k <= #[trigger] b[k] <= k + 1,
            i <= N,
            sum >= 0,
            a[( i ) as int] >= 1,  // Added by AI, ensuring the value of a[i] is at least 1 to prevent underflow
            a[( i ) as int] <= 100,  // Added by AI, setting an upper bound to prevent overflow
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N,
                b.len() == N,
                forall|k: int| k <= #[trigger] b[k] <= k + 1,
                i <= N,
                j <= i,
                sum >= 0,
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




//             a.set(i, a[i] - 1);
//   None: a[i] - 1

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True