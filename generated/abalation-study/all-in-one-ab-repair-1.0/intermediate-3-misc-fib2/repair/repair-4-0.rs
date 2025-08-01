
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

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
                2 <= i <= n,                          // i should be bounded between 2 and n
                fib.len() == i,                       // Length of the fib array should be equal to i
                fibo_fits_i32(n as int),              // fibo(n) should fit in i32
                forall|j: int| 0 <= j < i ==> #[trigger] fib[j] == fibo(j),
        {
            let next_fib = fib[i - 1] + fib[i - 2];
            proof {
                assert(0 <= i - 1 < i);
                assert(0 <= i - 2 < i);
                assert(fibo(i as int) == fibo(i as int - 1) + fibo(i as int - 2));
            }
            fib.push(next_fib);
            i += 1;
            // Additional proof block to confirm loop invariants stay consistent on each iteration
            proof {
                assert(fibo_fits_i32(n as int));
                assert(fib.len() == i);
                assert(forall|j: int| 0 <= j < i ==> #[trigger] fib[j] == fibo(j));
            }
        }
        ret
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpdca6wavr`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False