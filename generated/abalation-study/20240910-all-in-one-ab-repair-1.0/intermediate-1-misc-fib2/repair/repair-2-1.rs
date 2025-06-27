
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}
verus! {
    // Isolation flag for loop verification (assuming it's needed here).
    // #[verifier::loop_isolation(false)] 

    // Specification function to calculate the nth Fibonacci number.
    spec fn fibo(n: int) -> nat
        decreases n, // Indicates that the value of n decreases in recursive calls.
    {
        if n <= 0 {
            0
        } else if n == 1 {
            1
        } else {
            fibo(n - 2) + fibo(n - 1)
        }
    }

    // Specification to check if the Fibonacci number fits within an i32 integer.
    spec fn fibo_fits_i32(n: int) -> bool {
        fibo(n) < 0x8000_0000 // Ensures the value is within the 32-bit signed integer range.
    }

    // Function to generate a vector of Fibonacci numbers up to the nth element.
    fn fibonacci(n: usize) -> (ret: Vec<i32>)
        requires
            fibo_fits_i32(n as int), // Precondition that the nth Fibonacci number fits in an i32.
            n >= 2,                  // Precondition that n is at least 2.
        ensures
            forall|i: int| 2 <= i < n ==> #[trigger] ret@[i] == fibo(i), // Ensures the Fibonacci sequence is correct starting from the 2nd index.
            ret@.len() == n, // Ensures the length of the result vector is n.
    {
        // Initialize the Fibonacci vector with the first two Fibonacci numbers.
        let mut fib = Vec::new();
        fib.push(0);
        fib.push(1);
        let mut i = 2;
        
        // Loop to calculate the rest of the Fibonacci sequence.
        while i < n
            invariant
                2 <= i <= n,
                fib.len() == i,
                fibo_fits_i32(n as int), // Ensure fibo fits in i32, remains true.
                forall|j: int| 0 <= j < i ==> #[trigger] fib[j] == fibo(j), // Ensure all calculated Fibonacci numbers are correct.
        {
            let next_fib = fib[i - 1] + fib[i - 2];
            fib.push(next_fib);
            i += 1;
        }

        // Return the result vector.
        fib
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp4jbio82c`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: True