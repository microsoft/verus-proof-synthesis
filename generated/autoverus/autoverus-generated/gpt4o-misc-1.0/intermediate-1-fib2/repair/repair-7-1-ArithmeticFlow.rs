
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

proof fn lemma_fibo_i32_bounds(n: int)
    requires
        n >= 0,
    ensures
        fibo(n) < 0x8000_0000
{
    // We can use induction on `n` to prove this.

    if n == 0 {
        // Base case: fibo(0) == 0
    } else if n == 1 {
        // Base case: fibo(1) == 1
    } else {
        // Inductive step: assume fibo(n-1) and fibo(n-2) are both less than 0x8000_0000
        lemma_fibo_i32_bounds(n-1);
        lemma_fibo_i32_bounds(n-2);
        // Since both fibo(n-1) and fibo(n-2) are bounded and positive,
        // their sum is also bounded.
        assert(fibo(n) == fibo(n-1) + fibo(n-2));
    }
}

fn fibonacci(n: usize) -> (ret: Vec<i32>)
    requires
        fibo_fits_i32(n as int),
        n >= 2,
    ensures
        forall|i: int| 2 <= i < n ==> # [trigger] ret@[i] == fibo(i),
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
        // Assertion to ensure there won't be overflow
        assert(fib[i - 1] as i64 + fib[i - 2] as i64 <= i32::MAX as i64); 
        
        let next_fib = fib[i - 1] + fib[i - 2];
        fib.push(next_fib);
        i += 1;

        // Invoke our lemma to show that the Fibonacci value fits within i32 bounds
        lemma_fibo_i32_bounds(i as int);
    }
    fib
}

} // verus!


//         let next_fib = fib[i - 1] + fib[i - 2];
//   None: fib[i - 1] + fib[i - 2]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False