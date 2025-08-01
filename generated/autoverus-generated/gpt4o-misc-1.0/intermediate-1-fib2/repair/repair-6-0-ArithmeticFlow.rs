
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
    fibo(n) < 0x8000_0000 // Equivalent to i32::MAX + 1
}

spec fn safe_fib_add(a: i32, b: i32) -> bool {
    a as i64 + b as i64 <= i32::MAX as i64
}

proof fn lemma_safe_fib(n: int)
    requires
        fibo_fits_i32(n),
        n >= 2,
    ensures
        forall|i: int| 2 <= i < n ==> {
            let fib_i_minus_1 = fibo(i - 1);
            let fib_i_minus_2 = fibo(i - 2);
            safe_fib_add(fib_i_minus_1 as i32, fib_i_minus_2 as i32)
        }
{
    // Unroll some Fibonacci values and prove they fit in i32 before induction
    assert!(fibo(2) == 1); // fibo(0) + fibo(1)
    assert!(fibo(3) == 2); // fibo(1) + fibo(2)

    // Inductive proof
    ensures_forall_by(|i: int| {
        requires((2 <= i < n) ==> { fibo(i) < 0x8000_0000 });
        ensures({ 
            let fib_i_minus_1 = fibo(i - 1);
            let fib_i_minus_2 = fibo(i - 2);
            safe_fib_add(fib_i_minus_1 as i32, fib_i_minus_2 as i32)
        });

        if 2 <= i < n {
            let fib_i_minus_1 = fibo(i - 1);
            let fib_i_minus_2 = fibo(i - 2);
            assert!(safe_fib_add(fib_i_minus_1 as i32, fib_i_minus_2 as i32));
        }
    });
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
        let next_fib = {
            let fib_i_minus_1 = fib[i - 1];
            let fib_i_minus_2 = fib[i - 2];
            assert!(safe_fib_add(fib_i_minus_1, fib_i_minus_2)) by {
                lemma_safe_fib(n as int);
            };
            fib_i_minus_1 + fib_i_minus_2
        };
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