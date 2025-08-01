
use vstd::prelude::*;
fn main() {}

verus! {
    #[spec]
    fn triangle(n: nat) -> nat {
        decreases n;
        if n == 0 {
            0
        } else {
            n + triangle((n - 1) as nat)
        }
    }

    #[verifier::recursive] // Indicate that this function is recursive
    #[requires(idx <= n)]
    #[requires(*sum == triangle(idx as nat))]
    #[requires(triangle(n as nat) < 0x1_0000_0000)]
    #[ensures(*sum == triangle(n as nat))]
    fn tail_triangle(n: u32, idx: u32, sum: &mut u32) {
        if idx < n {
            let next_idx = idx + 1;
            *sum = *sum + next_idx;
            tail_triangle(n, next_idx, sum);
        }
    }

    // Example usage (Make sure to comment out when actually verifying using Verus)
    #[verifier::proof]
    fn test() {
        let n: u32 = 10;
        let mut sum: u32 = triangle(0);
        tail_triangle(n, 0, &mut sum);
        assert!(sum == triangle(n as nat));
    }
}


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpo9y_osto`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False