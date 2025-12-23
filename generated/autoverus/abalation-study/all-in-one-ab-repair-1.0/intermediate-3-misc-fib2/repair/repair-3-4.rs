
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
                // invariants should be properly specified so that Verus can prove the correctness
                2 <= i <= n,
                fib.len() == i,
                fibo_fits_i32(n as int),
                forall|j: int| 0 <= j < i ==> #[trigger] fib[j] == fibo(j),
        {
            let next_fib = fib[i - 1] + fib[i - 2];
            fib.push(next_fib);
            i += 1;
        }
        proof {
            forall|i: int| {
                requires(2 <= i < n);
                ensures(ret@[i] == fibo(i));
                // We need to show that the loop invariant has maintained the correctness of the Fibonacci computation up to i
                // This part is to help the verifier know that the resulting vector `ret` is correct
                let j = i - 1;
                let k = i - 2;
                assert(fib[i] == fibo(i));
                assert(j >= 0 && k >= 0 && i < n);
                assert(ret@[j] == fibo(j) && ret@[k] == fibo(k));
            }
        }
        ret
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpngwc1qzp`)
// 

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4
// Safe: False