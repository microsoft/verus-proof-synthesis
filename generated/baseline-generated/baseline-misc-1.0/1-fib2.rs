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

    proof fn fibo_nonnegative(n: int)
    requires
        n >= 0
    ensures
        fibo(n) >= 0
    decreases n
    {
        if n > 1 {
            fibo_nonnegative(n - 1);
            fibo_nonnegative(n - 2);
        }
    }

    proof fn fibo_sum(n: int)
    requires
        n >= 2
    ensures
        fibo(n) == fibo(n - 1) + fibo(n - 2)
    decreases n
    {
        if n > 2 {
            fibo_sum(n - 1);
        }
    }

    fn fibonacci(n: usize) -> (ret: Vec<i32>)
    requires
        fibo_fits_i32(n as int),
        n >= 2,
    ensures
        forall |i: int| 2 <= i < n ==> #[trigger] ret@[i] == fibo(i), 
        ret@.len() == n,
    {
        let mut fib = Vec::new();
        fib.push(0);
        fib.push(1);
        let mut i = 2;

        while i < n
        invariant
            fib.len() == i,
            forall |j: int| 0 <= j < i ==> fib@.index(j) == fibo(j),
            i >= 2
        {
            let next_fib = fib[i - 1] + fib[i - 2];

            proof {
                let j = i as int;
                assert(j >= 2);
                fibo_sum(j);
                fibo_nonnegative(j - 1);
                fibo_nonnegative(j - 2);
            }

            fib.push(next_fib);
            i += 1;
        }

        proof {
            assert forall |i: int| 2 <= i < n implies fib@.index(i) == fibo(i) by {
                // This assertion holds due to the loop invariant
            };
        }

        fib
    }
}

// Score: (3, 3)
// Safe: True