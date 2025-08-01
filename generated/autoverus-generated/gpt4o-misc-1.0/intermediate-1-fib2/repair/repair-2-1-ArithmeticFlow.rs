
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

proof fn lemma_monotonic_fibo_in_i32(i: int, j: int)
    requires
        i <= j,
        i >= 0,
    ensures
        fibo(i) <= fibo(j),
        fibo[i] + fibo[j] <= 0x7FFF_FFFF, // max positive value for i32
{
    // This function ensures that as we progress in the Fibonacci sequence, 
    // the numbers stay within the bounds of i32.
    if i > 1 {
        lemma_monotonic_fibo_in_i32(i-1, j-1);
        lemma_monotonic_fibo_in_i32(i-2, j-2);
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
        // Assert the next element is within bounds before the addition
        assert (fib[i - 1] as u64 + fib[i - 2] as u64) <= 0x7FFF_FFFF by {
            lemma_monotonic_fibo_in_i32((i-1) as int, (i-2) as int);
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