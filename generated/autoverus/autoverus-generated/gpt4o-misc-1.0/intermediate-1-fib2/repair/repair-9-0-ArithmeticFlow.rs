
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

// Lemma to ensure the growth of Fibonacci sequence
proof fn lemma_fibo_fits_i32(i: int, j: int)
    requires
        i <= j,
    ensures
        fibo(i) <= fibo(j),
{
    if i < j {
        lemma_fibo_fits_i32(i + 1, j);
        lemma_fibo_fits_i32(i + 2, j);
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
            // Additional invariant to check next value's validity
            forall|k: int| 0 <= k < i ==> fibo_fits_i32(k),
    {
        // Check next value does not cause overflow
        assert(fib[i - 1] as i64 + fib[i - 2] as i64 <= i32::MAX as i64) by {
            lemma_fibo_fits_i32(i as int - 1, n as int);
            lemma_fibo_fits_i32(i as int - 2, n as int);
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
// Safe: True