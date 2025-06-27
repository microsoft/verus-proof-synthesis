
use vstd::prelude::*;
fn main() {}

verus! {
    /// A recursive specification function that calculates the triangular number.
    spec fn triangle(n: nat) -> nat
        decreases n 
    {
        if n == 0 {
            0
        } else {
            n + triangle((n - 1) as nat)
        }
    }

    /// An implementation function for calculating the triangular number using tail recursion.
    #[verifier::proof]
    fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
        requires
            idx <= n,
            *sum as nat == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *sum as nat == triangle(n as nat),
        decreases (n - idx) as nat
    {
        if idx < n {
            let idx = idx + 1;
            *sum = *sum + idx;
            tail_triangle(n, idx, sum);
        }
    }
    
    // Verification function to initiate tail recursion with proper precondition.
    #[verifier::proof]
    pub fn verify_tail_triangle(n: u32) -> u32
        ensures
          result as nat == triangle(n as nat),
    {
        let mut sum = 0;
        tail_triangle(n, 0, &mut sum);
        sum
    }
}



// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp98duh9r_`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False