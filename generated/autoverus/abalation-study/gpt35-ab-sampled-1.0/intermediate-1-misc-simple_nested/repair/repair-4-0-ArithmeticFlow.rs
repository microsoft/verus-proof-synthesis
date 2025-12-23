
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
            b.len() == N,
            forall|k: int| k <= # [trigger] b[k] <= k + 1,
            i <= N as usize,
            old(a).len() == N,
            sum <= 2 * N,
            sum >= N,
            a.len() == N, 
            i >= 0,
            a[( i ) as int] - 1 >= std::i32::MIN, // Added by AI, preventing arithmetic underflow
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                j <= i,
                a.len() == N, 
                j >= 0,
                a[( i ) as int] - 1 >= std::i32::MIN, // Added by AI, preventing arithmetic underflow
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

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True