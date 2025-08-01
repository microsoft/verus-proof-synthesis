
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
            a.len() == N as usize,
            i <= N as usize,
            forall|k: int| k < i ==> a[k] > 0, // Added by AI, ensures that a[k] is always positive before subtraction
            sum <= 2 * N, // Added by AI
            sum >= N, // Added by AI
            a[( i ) as int] <= N, // Added by AI, a[i] will not exceed N
            a[( i ) as int] >= 0, // Added by AI, a[i] is non-negative
        {
        a.set(i, b[i] + 1);
        proof {
            assert(forall |k: int| k <= i ==> a[k] > 0); // AI: Adjusted forall condition
        }
        let mut j: usize = 0;
        assert(forall |k: int| k < i ==> a[k] > 0); // Added by AI
        while (j < i)
            invariant
                a.len() == N as usize,
                j <= i,
                a[( i ) as int] > 0, // Added by AI, ensures that a[i] is positive before subtraction
        {
            proof {
                assert(forall |k: int| k < i ==> a[k] > 0); // Added by AI
                assert(a[( i ) as int] > 0); // Added by AI
            }
            a.set(i, a[i] - 1); // This line has potential for underflow
            j = j + 1;
            proof {
                assert(forall |k: int| k < i ==> a[k] > 0); // Added by AI, ensures that a[k] is always positive before subtraction
            }
        }
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!

// Score: (0, 2)
// Safe: False