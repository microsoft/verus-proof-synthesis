
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
            a[( i ) as int] > 0, // Added by AI, ensures that a[i] is always positive before addition to sum
            sum <= 2 * N, // Added by AI, upper bound for sum
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N as usize,
                j <= i,
                forall|k: int| k < i ==> a[k] > 0, // Added by AI, ensures that a[k] is always positive before subtraction
        {
            a.set(i, a[i] - 1); // This line has potential for underflow
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