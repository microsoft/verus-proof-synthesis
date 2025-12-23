
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

// Lemma to show monotonicity of the Fibonacci sequence
proof fn lemma_fibo_monotonicity(i: int, j: int)
    requires
        i <= j,
    ensures
        fibo(i) <= fibo(j),
    decreases j - i
{
    if i < j {
        lemma_fibo_monotonicity(i, j - 1);
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
        // Add assertion to ensure no overflow
        assert(fibo(i as int - 1) + fibo(i as int - 2) < 0x8000_0000) by {
            lemma_fibo_monotonicity(i as int - 1, n as int);
            lemma_fibo_monotonicity(i as int - 2, n as int);
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

// Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 4
// Safe: True