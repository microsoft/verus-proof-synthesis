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

proof fn lemma_fibo_monotonic(n: int, m: int)
    requires
        n <= m,
    ensures
        fibo(n) <= fibo(m),
    decreases m - n // Changed by AI
{
    if n < m {
        lemma_fibo_monotonic(n, m - 1);
        assert(fibo(n) <= fibo(m - 1)); // Added by AI
        assert(fibo(m - 1) <= fibo(m));
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
    
    // Assert the invariant right before the loop starts
    assert(fib.len() == 2);
    
    while i < n
        invariant
            0 <= 2 <= i <= n,
            fib.len() == i,
            fibo_fits_i32(n as int),
            forall|j: int| 0 <= j < i ==> # [trigger] fib[j] == fibo(j),
            i <= n,
            fibo_fits_i32(n as int),
            n >= 2,
    {
        // Assert the addition won't overflow an i32
        assert((fib[i - 1] as int + fib[i - 2] as int) < 0x8000_0000) by {
            assert(i as int - 1 >= 0 && i as int - 2 >= 0);
            assert(fib[i - 1] as int == fibo(i as int - 1));
            assert(fib[i - 2] as int == fibo(i as int - 2));
            assert(fibo(i as int - 1) + fibo(i as int - 2) == fibo(i as int));
            lemma_fibo_monotonic(i as int, n as int);
        };
        
        let next_fib = fib[i - 1] + fib[i - 2];
        fib.push(next_fib);
        i += 1;
    }

    // Ensure the invariant holds after the loop
    assert(fib.len() == n);
    
    fib
}

} // verus!

// failed this postcondition
//         fibo(n) <= fibo(m),
// at the end of the function body
// {
//     if n < m {
//         lemma_fibo_monotonic(n, m - 1);
//     }
// }
//   at the end of the function body: {     if n < m {         lemma_fibo_monotonic(n, m - 1);     } }
//   failed this postcondition: fibo(n) <= fibo(m)

// Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: True