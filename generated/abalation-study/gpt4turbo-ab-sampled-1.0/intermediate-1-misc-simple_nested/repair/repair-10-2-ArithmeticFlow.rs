
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
    }
    while (i < N as usize)
        invariant
            0 <= sum,
            sum + b[(i) as int] + 1 <= 2 * N,
            sum <= 2 * i as i32, // Ensuring the upper bound of sum
            sum >= i as i32, // Ensuring the lower bound of sum
            N <= 0x3FFF_FFFF,
            a.len() == N as usize,
            b.len() == N as usize,
            forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1, // Adjusted to correctly reflect relationship between 'a' and 'b'
            forall|k: int| k <= # [trigger] b[k] <= k + 1,
            i <= N as usize,
            0 <= i, // Ensuring i is non-negative.
            sum + 1 <= 2 * N, // Ensuring that sum + a[i] will not exceed the arithmetic upper bound.
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N as usize,
                b.len() == N as usize,
                j <= i,
                N <= 0x3FFF_FFFF,
                // invariant for the relationship between 'a' and 'b' with adjustment for the decrement in 'a'
                forall|k: int| 0 <= k < i ==> a[k] == b[k], 
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