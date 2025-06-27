
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
        fibo(n) < 0x8000_0000  // 2,147,483,648
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
        assert(fib.push(0).is_ok()); // Ensuring push() results are handled
        assert(fib.push(1).is_ok());
        
        let mut i = 2;          
        while i < n
            invariant
                2 <= i <= n,
                fib.len() == i,
                fibo_fits_i32(i as int),
                forall|j: int| 0 <= j < i ==> #[trigger] fib[j] == fibo(j),
        {
            let next_fib = fib[i - 1] + fib[i - 2];
            proof {
                assert(0 <= i - 1 < i as int);
                assert(0 <= i - 2 < i as int);
                assert(fibo(i as int) == fibo(i as int - 1) + fibo(i as int - 2));
            }
            assert(fib.push(next_fib).is_ok());
            i += 1;
        }
        fib
    }
} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmp3s0k4abw`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False