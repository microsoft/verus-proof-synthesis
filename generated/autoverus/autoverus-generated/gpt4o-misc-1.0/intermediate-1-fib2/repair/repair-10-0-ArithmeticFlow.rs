
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

// Lemma to establish the monotonicity and bounds of the Fibonacci sequence
proof fn lemma_fibo_bounds(n: int)
    requires
        n >= 0,
    ensures
        fibo(n) < 0x8000_0000, // ensures it fits within i32 bounds
    decreases n
{
    if n > 1 {
        lemma_fibo_bounds(n - 1);
        lemma_fibo_bounds(n - 2);
        assert(fibo(n) < 0x8000_0000); // Ensure that it holds for all n >= 0
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
            2 <= i <= n,
            fib@.len() == i,
            forall|j: int| 2 <= j < i ==> fib@.index(j) == fibo(j),
            fib.len() == i,
            fibo_fits_i32(i as int),
    {
        // Assertion to ensure no overflow
        assert({
            let f1 = fibo((i - 1) as int);
            let f2 = fibo((i - 2) as int);
            f1 + f2 < 0x8000_0000
        }) by {
            lemma_fibo_bounds((i - 1) as int);
            lemma_fibo_bounds((i - 2) as int);
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

// Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 5
// Safe: True