
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

// Lemma function to prove the Fibonacci sequence's monotonicity and bounds
proof fn lemma_fibo_monotonic_and_bounded(i: int, upper_bound: nat)
    requires
        2 <= i,
        fibo(i) < upper_bound,
    ensures
        fibo(i - 1) + fibo(i - 2) < upper_bound,
    decreases i
{
    assert(fibo(i - 1) + fibo(i - 2) == fibo(i)) by {

        // Inductive proof for Fibonacci calculation:
        // fibo(i) = fibo(i - 1) + fibo(i - 2)
        if i <= 1 {
            // Base case handled by fibo function directly
        } else {
            lemma_fibo_monotonic_and_bounded(i - 1, upper_bound); // Recursive proof
            lemma_fibo_monotonic_and_bounded(i - 2, upper_bound);
        }
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
        assert(fib[i - 1] >= 0 && fib[i - 2] >= 0); // Ensure no underflow
        assert(i as int >= 2); // Ensure we are in bounds
        assert({
            lemma_fibo_monotonic_and_bounded(i as int, 0x8000_0000);
            true // The assertion itself
        });

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
// Safe: True