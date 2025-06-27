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
    proof {
        assert(forall|k: int| 0 <= k < 0 ==> a[k] == b[k]); // Initial condition for the loop.
        assert(sum + b[0] + 1 <= 2 * N); // Ensuring the upper bound before the loop starts
    }
    while (i < N as usize)
        invariant
            0 <= sum,
            sum + b[(i) as int] <= sum + (i as i32) + 1, // Upper bound considering maximum value of b[i] and loop increment, adjusted correctly to prevent overflow.
            sum <= 2 * i as i32, // Correction for the sum upper bound within the loop
            sum >= i as i32, // Lower bound on sum based on the modification inside the loop
            N <= 0x3FFF_FFFF,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k] == b[k], // Corrected by AI
            forall|k: int| k <= # [trigger] b[k] <= k + 1,
            i <= N as usize,
            sum + a[( i ) as int] <= 2 * N, // Added upper bound loop invariant for sum after the addition
            sum >= 0, // Ensuring sum does not go below 0, preventing underflow
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N as usize, // Invariant specifies the length of the array "a".
                b.len() == N as usize, // Invariant specifies the length of the array "b".
                j <= i,
                N <= 0x3FFF_FFFF,
                forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1, // Correctly reflect the update to 'a' in loop's invariant
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


//         sum = sum + a[i];
//   None: sum + a[i]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True