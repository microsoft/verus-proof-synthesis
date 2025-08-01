
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
            i <= n,
            fib@.len() == i as int,
            forall |j: int| 0 <= j < i ==> fib[j] == fibo(j),
            fibo_fits_i32(n as int),
            n >= 2,
    {

        let next_fib = fib[i - 1] + fib[i - 2];

        fib.push(next_fib);
        
        i += 1;
    }

    ret
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1