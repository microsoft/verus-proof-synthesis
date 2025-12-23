
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
    fibo(n) < 0x8000_0000 // Maximum value for i32, i.e., 2^31 - 1
}

proof fn fib_is_monotonic(n: int)
    requires
        n >= 0,
    ensures
        forall|i: int, j: int| 0 <= i <= j <= n ==> fibo(i) <= fibo(j)
{
    if n == 0 || n == 1 {
        // Base cases: trivially true
    } else {
        fib_is_monotonic(n - 1);
        fib_is_monotonic(n - 2);
        assert(fibo(n - 2) + fibo(n - 1) == fibo(n));
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
        assert(fib[i - 1] as nat + fib[i - 2] as nat <= fibo(i as int)) by {
            fib_is_monotonic(i as int);
        };
        let next_fib = fib[i - 1] + fib[i - 2];
        assert(next_fib as nat <= 0x8000_0000); // Ensure it fits in i32
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