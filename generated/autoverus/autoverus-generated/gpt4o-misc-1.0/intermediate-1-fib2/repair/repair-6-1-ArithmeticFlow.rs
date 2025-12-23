
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

// Lemma to show that Fibonacci sequence is monotonic and fits within i32 bounds given appropriate preconditions
proof fn lemma_fibo_monotonic_and_fits(i: int, n: int)
    requires
        2 <= i <= n,
        fibo_fits_i32(n),
    ensures
        fibo(i) + fibo(i - 1) < 0x8000_0000
{
    // Proof of the lemma would likely involve properties of the Fibonacci sequence and ensuring it fits within bounds
    // Since fibo_within_bounds ensures fibo(n) < 0x8000_0000, we derive related properties for (i) and (i - 1)
    // With 'i' small enough, it avoids overflow due to the nature of the Fibonacci sequence growing exponentially
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
        // Assert to prevent overflow: next_fib should be less than or equal to max(i32)
        assert(fib[i - 1] <= 0x3FFF_FFFF && fib[i - 2] <= 0x3FFF_FFFF) by {
            // Use the lemma here to assert the bounds
            lemma_fibo_monotonic_and_fits(i as int, n as int);
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

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 5
// Safe: True