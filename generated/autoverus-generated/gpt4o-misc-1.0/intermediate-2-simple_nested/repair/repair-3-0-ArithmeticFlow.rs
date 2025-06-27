
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
    while (i < N as usize)
        invariant
            N <= 0x3FFF_FFFF,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1,
            i <= N as usize,
            sum <= 2 * i as i32,
            sum >= i as i32,
            N <= 0x3FFF_FFFF,
    {
        a.set(i, b[i] + 1);
        
        // Assert the invariant before starting the inner loop.
        assert(forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1);
        
        let mut j: usize = 0;
        while (j < i)
            invariant
                // adding 'forall|k: int| 0 <= k < j' since array a is not modified in this loop
                forall|k: int| 0 <= k < j ==> a[k] == b[k] + 1,
                forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1, // Fixed invariant
                j <= i,
                N <= 0x3FFF_FFFF,
                a.len() == N,
                b.len() == N,
                a[( i ) as int] > 0,       // lower bound for a[i]
                a[( i ) as int] <= 0x4000_0001, // upper bound for a[i] (since b[i] + 1 <= N + 1 <= 0x4000_0001)
        {
            a.set(i, a[i] - 1);
            j = j + 1;

            proof {
                assert(forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1);
            } // Added by AI
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