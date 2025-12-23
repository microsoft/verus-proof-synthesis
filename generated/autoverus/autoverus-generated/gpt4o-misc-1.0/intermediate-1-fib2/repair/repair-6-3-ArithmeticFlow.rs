
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
    fibo(n) < 0x8000_0000 // Ensure the Fibonacci value fits within i32 bounds
}

proof fn lemma_fibo_monotonic(n: int)
    requires
        n >= 0,
    ensures
        fibo(n + 1) >= fibo(n),
{
    if n < 2 {
        // Base cases are trivially true
        return;
    } else {
        lemma_fibo_monotonic(n - 1);
    }
}

proof fn lemma_fibo_sum_within_bounds(a: int, b: int)
    requires
        a >= 0, b >= 0,
        fibo(a) < 0x4000_0000,  // Ensure individual values fit within i32/2
        fibo(b) < 0x4000_0000,
    ensures
        fibo(a) + fibo(b) < 0x8000_0000,
{
    assert(fibo(a) + fibo(b) < 0x8000_0000); // Directly follows from the bounds
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
            2 <= i <= n,
            fib@.len() == i,
            forall|j: int| 2 <= j < i ==> fib@.index(j) == fibo(j),
            fib.len() == i,
    {
        // Assert that adding the two previous Fibonacci numbers will not overflow
        assert(fib[i - 1] as int + fib[i - 2] as int < 0x8000_0000) by {
            lemma_fibo_sum_within_bounds(i as int - 1, i as int - 2);
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