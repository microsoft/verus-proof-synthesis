
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
    fibo(n) < 0x8000_0000 // 2^31
}

// Monotonicity lemma for the Fibonacci sequence to help with bounds
proof fn lemma_fibo_monotonic(i: int)
    requires
        0 <= i,
    ensures
        fibo(i) <= fibo(i + 1)
{
    // This is a simple property of the Fibonacci sequence
    match i {
        0 => { assert(fibo(0) == 0 && fibo(1) == 1); }
        1 => { assert(fibo(1) == 1 && fibo(2) == 1); }
        _ => {
            lemma_fibo_monotonic(i - 1);
            lemma_fibo_monotonic(i - 2);
            assert(fibo(i) <= fibo(i + 1));
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
    fib.push(0); // Initial element corresponding to fibo(0)
    fib.push(1); // Initial element corresponding to fibo(1)
    let mut i = 2;
    while i < n
        invariant
            2 <= i <= n,
            fib@.len() == i,
            forall|j: int| 2 <= j < i ==> fib@.index(j) == fibo(j),
            fib.len() == i,
    {
        // Assert that the next Fibonacci number will fit within i32 bounds
        assert(fibo(i as int - 1) + fibo(i as int - 2) < 0x8000_0000) by {
            lemma_fibo_monotonic(i as int - 2);
            lemma_fibo_monotonic(i as int - 1);
        };

        let next_fib: i32 = fib[i - 1] + fib[i - 2];
        fib.push(next_fib);
        i += 1;
    }
    fib
}

} // verus!


//         let next_fib = fib[i - 1] + fib[i - 2];
//   None: fib[i - 1] + fib[i - 2]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False