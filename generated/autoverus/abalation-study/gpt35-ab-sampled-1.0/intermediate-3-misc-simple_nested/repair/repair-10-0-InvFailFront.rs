
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
        proof {
            assert(a[i as int] >= 1); // Added by AI, ensuring the value of a[i] is at least 1 to prevent underflow
        }
        while (i < N as usize)
            invariant
                N <= 0x3FFF_FFFF,
                a.len() == N,
                b.len() == N,
                forall|k: int| k <= #[trigger] b[k] <= k + 1,
                i <= N,
                sum >= 0,
                a[( i ) as int] >= 1,  // Added by AI, ensuring the value of a[i] is at least 1 to prevent underflow
                a[( i ) as int] <= 100,  // Added by AI, setting an upper bound on a[i] to prevent overflow
                sum + a[( i ) as int] >= i,  // Added by AI, ensuring the sum + a[i] does not underflow
                sum + a[( i ) as int] <= 200,  // Added by AI, setting an upper bound on sum + a[i] to prevent overflow
            {
                a.set(i, b[i] + 1);
                let mut j: usize = 0;
                while (j < i)
                    invariant
                        a.len() == N,
                        b.len() == N,
                        forall|k: int| k <= #[trigger] b[k] <= k + 1,
                        i <= N,
                        j <= i,
                        sum >= 0,
                        a[( i ) as int] >= 1,  // Added by AI, ensuring the value of a[i] is at least 1 to prevent underflow in the nested loop
                        a[( i ) as int] <= 100,  // Added by AI, setting an upper bound on a[i] to prevent overflow in the nested loop
                    {
                        a.set(i, a[i] - 1);
                        j = j + 1;
                        // assert(a[i as int] >= 1); // Uncommented by AI, ensuring the value of a[i] is at least 1 to prevent underflow in the nested loop
                        // assert(a[i as int] <= 100); // Uncommented by AI, setting an upper bound on a[i] to prevent overflow in the nested loop
                    }
                sum = sum + a[i];
                i = i + 1;
            }
        sum
    }
}


//                 a[( i ) as int] <= 100,  // Added by AI, setting an upper bound on a[i] to prevent overflow
//   None: a[( i ) as int] <= 100

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 5
// Safe: True