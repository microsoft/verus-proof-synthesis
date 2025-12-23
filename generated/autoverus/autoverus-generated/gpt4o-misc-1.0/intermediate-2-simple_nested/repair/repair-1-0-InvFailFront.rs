
use vstd::prelude::*;
fn main() {}

verus! {

    #[verifier::loop_isolation(false)]

    pub fn simple_nested(a: &mut Vec<i32>, b: &Vec<i32>, N: i32) -> (sum: i32)
        requires
            forall|k: int| k <= b[k] <= k + 1,
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
                forall|k: int| 0 <= k < i ==> a[k] == b[k] + 1 - (i - 1) as i32,
                i <= N as usize,
                sum <= 2 * i as i32,
                sum >= i as i32,
                N <= 0x3FFF_FFFF,
        {
            a.set(i, b[i] + 1);
            assert(forall|k: int| 0 <= k < a.len() ==> a[k] == b[k] + 1 - (i as i32 - 1)); // Assertion before the inner loop

            let mut j: usize = 0;
            while (j < i)
                invariant
                    forall|k: int| 0 <= k < j ==> a[k] == b[k] + 1 - (j - 1) as i32,
                    j <= i,
                    N <= 0x3FFF_FFFF,
                    a.len() == N,
                    b.len() == N,
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


//                 forall|k: int| 0 <= k < a.len() ==> a[k] == b[k] + 1 - (j - 1) as i32, // Checking all elements in 'a' array
//   None: forall|k: int| 0 <= k < a.len() ==> a[k] == b[k] + 1 - (j - 1) as i32

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False