
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
    fibo(n) <= 0x7FFF_FFFF // Integer.MAX_VALUE for i32
}

spec fn fibo_value(i: int) -> nat
     recommends i >= 0 ==> fibo_fits_i32(i as int),
     {
        fibo(i)
     }

proof fn lemma_fibo_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fibo(i as int) <= fibo(j as int),
    decreases j
{
    // The Fibonacci sequence is non-decreasing for positive n:
    if i < j {
        lemma_fibo_monotonic(i, ( j - 1 ) as nat);
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
            2 <= i <= n,
            fib@.len() == i,
            forall|j: int| 2 <= j < i ==> fib@.index(j) == fibo(j),
            fib.len() == i,
    {
        assert((fib[i - 1] as nat) + (fib[i - 2] as nat) <= 0x7FFF_FFFF) by {
            lemma_fibo_monotonic((i-1) as nat, (i-1) as nat);
            lemma_fibo_monotonic((i-2) as nat, (i-2) as nat);
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