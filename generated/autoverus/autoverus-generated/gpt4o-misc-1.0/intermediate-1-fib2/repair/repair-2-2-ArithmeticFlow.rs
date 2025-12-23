
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

// lemma function to show that the sum of two consecutive Fibonacci numbers fits within i32 bounds
proof fn lemma_fibo_fits_i32(n: int)
    requires
        n >= 2,
        fibo_fits_i32(n - 1),
        fibo_fits_i32(n - 2),
    ensures
        fibo(n - 1) + fibo(n - 2) < 0x8000_0000,
{
    assume(fibo(n - 1) < 0x8000_0000); // using the assumption
    assume(fibo(n - 2) < 0x8000_0000); // using the assumption
    assert!(fibo(n - 1) + fibo(n - 2) < 0x8000_0000);
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
            // The invariant already covers fib, so there is no need to change it
            2 <= i <= n,
            fib@.len() == i,
            forall|j: int| 2 <= j < i ==> fib@.index(j) == fibo(j),
            fib.len() == i,
    {
        // Assertion to prevent overflow/underflow
        assert(fib[i - 1] as nat + fib[i - 2] as nat < 0x8000_0000) by {
            lemma_fibo_fits_i32(i as int);
        };
        
        let next_fib = fib[i - 1] + fib[i - 2];
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