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

fn fibonacci(n: usize) -> (ret: Vec<i32>)
requires
    fibo_fits_i32(n as int),
    n >= 2,
ensures
    forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] ==  fibo(i), 
    ret@.len() == n,
{
    let mut fib = Vec::new();
    fib.push(0);
    fib.push(1);
    let mut i = 2;

    while i < n
        invariant
            fib.len() == i, 
            i <= n,
            forall |k: int| 2 <= k < i ==> fib@[k] == fibo(k),
    {

        let next_fib = fib[i - 1] + fib[i - 2];

        fib.push(next_fib);
        
        i += 1;
    }

    fib
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 6