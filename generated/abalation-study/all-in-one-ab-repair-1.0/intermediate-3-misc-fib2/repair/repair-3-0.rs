
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
                // invariants to ensure correctness
                2 <= i <= n,
                fib.len() == i,
                fibo_fits_i32(n as int),
                forall|j: int| 0 <= j < i ==> #[trigger] fib[j] == fibo(j),
        {
            let next_fib = fib[i - 1] + fib[i - 2];
            // Ensuring `next_fib` fits in i32 and parameterized with invariant
            proof {
                assert(next_fib == fibo(i));
                assert(fibo_fits_i32(n as int));
            }
            fib.push(next_fib);
            i += 1;
        }
        fib
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpn31oqmnq`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: True