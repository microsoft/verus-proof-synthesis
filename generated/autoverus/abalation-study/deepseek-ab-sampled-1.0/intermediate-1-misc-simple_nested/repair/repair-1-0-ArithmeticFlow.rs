

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
            forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1 - k,
            i <= N,
            sum <= 2 * N,
            sum >= N,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                a.len() == N,
                b.len() == N,
                a[(i) as int] == b[(i) as int] + 1 - j,
                i <= N,
                j <= i,
                sum <= 2 * N,
                sum >= N,
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        assert!((sum <= i32::MAX)); // Add this assertion to prevent overflow
        assert!((sum >= i32::MIN)); // Add this assertion to prevent underflow
        i = i + 1;
    }
    sum
}

} // verus!

//         sum = sum + a[i];
//   None: sum + a[i]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False