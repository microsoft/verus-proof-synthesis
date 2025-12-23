#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
    spec fn fibo(n: int) -> nat
    decreases n
{
    if n <= 0 { 0 } else if n == 1 { 1 }
    else { fibo(n - 2) + fibo(n - 1) }
}

spec fn fibo_fits_i32(n: int) -> bool {
    fibo(n) < 0x8000_0000
}

proof fn proof_lemma_fibo_add(i: int)
    requires 
        i >= 2,
    ensures
        fibo(i) == fibo(i-1) + fibo(i-2),
    decreases i
{
    // base case for recursion
    if i == 2 {
        // Just to make sure the definition holds at base case
        assert(fibo(i) == 1);
        assert(fibo(i - 1) == 1);
        assert(fibo(i - 2) == 0);
    }
}

fn fibonacci(n: usize) -> (ret: Vec<i32>)
requires
    fibo_fits_i32(n as int),
    n >= 2,
ensures
    forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] ==  fibo(i), 
    ret@.len() == n,
{
    let mut fib = Vec::new();
    fib.push(0); // fib[0]
    fib.push(1); // fib[1]
    let mut i = 2;

    while i < n
        invariant
            2 <= i <= n,
            fib.len() == i,
            forall |j: int| 2 <= j < i ==> fib[j] == fibo(j)
    {
        let next_fib = fib[i - 1] + fib[i - 2];
        proof {
            // Ensure next_fib is equal to fibo(i)
            proof_lemma_fibo_add(i as int);
        }
        fib.push(next_fib);
        i += 1;
    }

    fib
}
}
// Score: (3, 2)
// Safe: True