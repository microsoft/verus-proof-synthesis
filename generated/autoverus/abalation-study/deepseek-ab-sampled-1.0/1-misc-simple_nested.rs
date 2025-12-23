
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
            i <= N,
            sum >= i as i32, // Corrected lower bound
            sum <= 2 * i as i32, // Corrected upper bound
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
                sum >= i as i32,
                sum <= 2 * i as i32,
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


// Score: (1, 0)
// Safe: True