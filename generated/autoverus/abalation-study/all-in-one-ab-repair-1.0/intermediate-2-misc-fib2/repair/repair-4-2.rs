
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
        fibo(n) < 0x8000_0000 // Ensure the calculated Fibonacci number fits in a i32
    }

    fn fibonacci(n: usize) -> (ret: Vec<i32>)
        requires
            fibo_fits_i32(n as int),
            n >= 2,
        ensures
            forall|i: int| 0 <= i < n ==> #[trigger] ret@[i] == fibo(i),
            ret@.len() == n,
    {
        let mut fib = Vec::new();
        fib.push(0);
        fib.push(1);

        let mut i = 2;
        while i < n
            invariant
                0 <= 2 <= i <= n,
                fib.len() == i,
                fibo_fits_i32(n as int),
                forall|j: int| 0 <= j < i ==> #[trigger] fib@[j] == fibo(j),
                n >= 2,
        {
            let next_fib = fib[i - 1] + fib[i - 2];
            proof {
                assert(fib[i - 1] == fibo(i as int - 1));
                assert(fib[i - 2] == fibo(i as int - 2));
                // Ensuring the sum fits the 32-bit integer limit
                assert(fib[i - 1] as int + fib[i - 2] as int == fibo(i as int - 1) + fibo(i as int - 2));
                assert(next_fib == fibo(i as int)); 
            }
            fib.push(next_fib);
            proof {
                assert(fib.len() == i + 1);
            }
            i += 1;
        }

        proof {
            assert(fib.len() == n); // Ensure fib.len() is n after the loop
            assert(forall|j: int| 0 <= j < n ==> fib@[j] == fibo(j)); // Ensure all elements match the Fibonacci sequence
        }

        fib
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpqq4y9h_w`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False