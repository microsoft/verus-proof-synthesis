
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
        fibo(n) < 0x8000_0000 // This ensures that the Fibonacci number fits within i32 limits
    }

    fn fibonacci(n: usize) -> (ret: Vec<i32>)
        requires
            fibo_fits_i32(n as int),
            n >= 2,
        ensures
            forall|i: int| 2 <= i < n ==> #[trigger] ret@[i] == fibo(i),
            ret@.len() == n,
    {
        let mut fib = Vec::new();
        fib.push(0); // Added first Fibonacci number
        fib.push(1); // Added second Fibonacci number
        let mut i = 2; // Start index from 2
        while i < n 
            invariant
                2 <= i <= n,
                fib.len() == i,
                fibo_fits_i32(n as int),
                forall|j: int| 0 <= j < i ==> #[trigger] fib@[j] == fibo(j),
        {
            let next_fib = fib[i - 1] + fib[i - 2];
            fib.push(next_fib);
            i += 1;
        }
        
        proof {
            // These assertions ensure the post-conditions
            assert(fib@.len() == n);
            assert(forall|i: int| 2 <= i < n ==> fib@[i] == fibo(i));
        }
        
        fib
    }
}

// Score: (2, 2)
// Safe: True