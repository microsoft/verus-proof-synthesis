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
            0 <= i <= N as usize,
            a.len() == N,
            b.len() == N,
            forall|k: int| 0 <= k < i ==> b[k] <= k + 1,
            sum <= i as i32 * 2,
            sum >= i as i32,
            N <= 0x3FFF_FFFF,
    {
        a.set(i, b[i] + 1);
        let mut j: usize = 0;
        while (j < i)
            invariant
                0 <= j <= i,
                a.len() == N,
                a[(i) as int] == b[(i) as int] + 1 - j as i32,
                b.len() == N,
                // b is never changed in the loop, so the invariant is updated to cover all elements
                forall |k:int| 0<= k < b.len() ==> b[k] <= k + 1,
                N <= 0x3FFF_FFFF,
        {
            a.set(i, a[i] - 1);
            j = j + 1;
        }
        sum = sum + a[i];
        i = i + 1;
        
        proof {
        } // Added by AI
    }
    sum
}

} // verus!

// Score: (1, 0)
// Safe: False