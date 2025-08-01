
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

proof fn lemma_fibo_monotonic(n: int)
    requires
        n >= 0,
    ensures
        fibo(n + 2) == fibo(n) + fibo(n + 1),
{
    if n == 0 {
        // The base cases for Fibonacci sequence
    } else {
        lemma_fibo_monotonic(n - 1);
    }
}

fn fibonacci(n: usize) -> (ret: Vec<i32>)
    requires
        fibo_fits_i32(n as int),
        n >= 2,
    ensures
        forall|i: int| 2 <= i < n ==> ret@.index(i) == fibo(i),
        ret@.len() == n,
{
    let mut fib = Vec::new();
    fib.push(0);
    fib.push(1);
    let mut i = 2;
    while i < n
        invariant
            2 <= i <= n,
            fib@.len() == i,
            forall|j: int| 2 <= j < i ==> fib@.index(j) == fibo(j),
            fib.len() == i,
    {
        let next_fib = {
            // Assertion to ensure there is no overflow
            assert((fib[i - 1] as i64 + fib[i - 2] as i64) < i32::MAX as i64);
            assert((fib[i - 1] as i64 + fib[i - 2] as i64) >= i32::MIN as i64);
            (fib[i - 1] as i64 + fib[i - 2] as i64) as i32
        };
        fib.push(next_fib);
        i += 1;
    }
    fib
}

} // verus!


//         let next_fib = fib[i - 1] + fib[i - 2];
//   None: fib[i - 1] + fib[i - 2]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False