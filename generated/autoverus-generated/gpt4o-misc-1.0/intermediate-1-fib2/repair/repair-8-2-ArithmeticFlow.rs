
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
    fibo(n) < 0x8000_0000 // Ensuring it fits within 32-bit signed integer bounds
}

// Lemma function to ensure monotonicity and bounds of Fibonacci sequence
proof fn lemma_fibo_monotonic(n: int)
    ensures
        forall|i: int| 2 <= i <= n ==> (fibo(i - 1) as i64) + (fibo(i - 2) as i64) < 0x8000_0000,
    decreases n
{
    // We use induction to prove the property
    if n >= 2 {
        lemma_fibo_monotonic(n - 1);
        lemma_fibo_monotonic(n - 2);
        assert(fibo(n - 1) as i64 + fibo(n - 2) as i64 <= 0x7FFF_FFFF); // 0x7FFF_FFFF = 0x8000_0000 - 1
    }
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
            2 <= i <= n,
            fib@.len() == i,
            forall|j: int| 2 <= j < i ==> fib@.index(j) == fibo(j),
            fib.len() == i,
    {
        assert(fib[i - 1] as i64 + fib[i - 2] as i64 < 0x8000_0000) by {
            lemma_fibo_monotonic(i as int);
        };
        
        let next_fib = fib[i - 1] + fib[i - 2];
        fib.push(next_fib);
        i += 1;
    }
    fib
}

} 


//         let next_fib = fib[i - 1] + fib[i - 2];
//   None: fib[i - 1] + fib[i - 2]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1
// Safe: False