
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

spec fn fibo_i32_bound(n: int) -> bool {
    fibo(n) <= 0x7FFF_FFFF
}

proof fn fibo_monotonic(n: int)
    requires
        n >= 2,
    ensures
        fibo(n-1) <= fibo(n),
        fibo(n-2) <= fibo(n),
        fibo(n-1) + fibo(n-2) <= 0x7FFF_FFFF,
{
    // Implementing the lemma using induction or other proof techniques 
    // is necessary to establish the required properties.
    if n > 2 {
        fibo_monotonic(n - 1);
        fibo_monotonic(n - 2);
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
        assert(fibo_i32_bound(i as int));
        assert(fib[i - 1] as int + fib[i - 2] as int <= 0x7FFF_FFFF); // Ensure the result won't overflow
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