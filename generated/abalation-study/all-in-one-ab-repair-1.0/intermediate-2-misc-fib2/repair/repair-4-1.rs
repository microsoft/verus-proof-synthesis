
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
    #[verifier::loop_isolation(false)]

    spec fn fibo(n: int) -> nat
        decreases n,
    {
        if n <= 0 {
            0
        } else if n == 1 {
            1
        } else {
            fibo(n - 2) + fibo(n - 1)
        }
    }

    spec fn fibo_fits_i32(n: int) -> bool {
        fibo(n) < 0x8000_0000 // Ensure it fits within i32 range
    }

    fn fibonacci(n: usize) -> (ret: Vec<i32>)
        requires
            fibo_fits_i32(n as int), // Pre-condition for i32 fit
            n >= 2,  // Pre-condition for minimum size n >= 2
        ensures
            forall|i: int| 2 <= i < n ==> #[trigger] ret@[i] == fibo(i),
            ret@.len() == n, // Post-condition ensuring final length
    {
        let mut fib = Vec::new();  // Initialize the vector
        fib.push(0); // Push first Fibonacci number
        fib.push(1); // Push second Fibonacci number
        let mut i = 2; // Start index at 2
        while i < n
            invariant
                2 <= i <= n,  // Ensure loop respects bounds
                fib.len() == i, // Ensure length matches index
                fibo_fits_i32(n as int), // Maintain precondition
                forall|j: int| 0 <= j < i ==> #[trigger] fib@[j] == fibo(j), // Maintain calculated Fibonacci values
                n >= 2,
        {
            let next_fib = fib[i - 1] + fib[i - 2]; // Calculate next Fibonacci number
            fib.push(next_fib); // Push to the vector
            i += 1; // Move to next index
        }

        proof {
            assert(fib.len() == n); // Ensure final length matches the expected `n`
        }

        fib
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp8sl97tcy`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: True