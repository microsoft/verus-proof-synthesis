use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
    requires
        forall|k: int| 0 <= k < N ==> 0 <= #[trigger] b[k] <= k + 1, // Corrected require clause with explicit range check
        old(a).len() == N as usize,
        b.len() == N as usize,
        N <= 0x3FFF_FFFF,
    ensures
        N <= sum <= 2 * N,
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize, // Corrected invariant to ensure the valid range
            N <= 0x3FFF_FFFF,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1, // Corrected invariant with explicit range check
            sum <= 2 * i as i32,
            sum >= i as i32,
    {
        a.set(i, b[i] + 1);

        // Assert the invariant before starting the inner loop.
        assert(forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1);

        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= j <= i, // Corrected invariant to ensure the valid range
                N <= 0x3FFF_FFFF,
                a.len() == N as usize,
                b.len() == N as usize,
                forall|k: int| 0 <= k < j ==> a[k] == b[k] + 1, 
                forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1, 
                a[( i ) as int] > 0,       // lower bound for a[i]
                a[( i ) as int] <= 0x4000_0001, // upper bound for a[i] (since b[i] + 1 <= N + 1 <= 0x4000_0001)
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        assert(sum + a[( i ) as int] <= 2 * (i + 1) as i32); // Assertion to prevent overflow
        assert(sum + a[( i ) as int] >= (i + 1) as i32); // Assertion to prevent underflow
        sum = sum + a[i];
        i = i + 1;
    }
    sum
}

} // verus!

//         assert(sum + a[( i ) as int] <= 2 * (i + 1) as i32); // Assertion to prevent overflow
//   assertion failed: sum + a[( i ) as int] <= 2 * (i + 1) as i32

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: False