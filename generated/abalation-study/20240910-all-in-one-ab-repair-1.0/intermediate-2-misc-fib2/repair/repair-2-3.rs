
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
        fibo(n) < 0x8000_0000
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
        fib.push(0);
        fib.push(1);
        let mut i = 2;
        while i < n
            invariant
                0 <= i <= n,
                fib.len() == i,
                fibo_fits_i32(n as int),
                forall|j: int| 0 <= j < i ==> #[trigger] fib@[j] == fibo(j), 
                n >= 2,
        {
            let next_fib = fib[i - 1] + fib[i - 2];
            fib.push(next_fib);
            i += 1;
        }

        proof {
            assert(fib.len() == n); 
        }

        fib
    }
} // verus!

Make sure to run verus with the correct command. Here’s an example assuming you have a file named `fibonacci.rs`:

shell
verus fibonacci.rs


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpboj90cni`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False