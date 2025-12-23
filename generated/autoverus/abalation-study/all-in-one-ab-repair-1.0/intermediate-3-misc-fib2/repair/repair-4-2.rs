
#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {

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

    fn fibonacci(n: usize) -> (ret: Vec<i32>)
        requires
            fibo_fits_i32(n as int),
            n >= 2,
        ensures
            forall|i: int| 2 <= i < n ==> ret@[i] == fibo(i),
            ret@.len() == n,
    {
        let mut fib = Vec::new();
        fib.push(0);
        fib.push(1);
        let mut i = 2;
        while i < n
            invariant
                2 <= i <= n,                          // i should be bounded between 2 and n
                fib.len() == i,                       // Length of the fib array should be equal to i
                fibo_fits_i32(n as int),              // fibo(n) should fit in i32
                forall|j: int| 0 <= j < i ==> fib@[j] == fibo(j),
        {
            let next_fib = fib[i - 1] + fib[i - 2];
            proof {
                assert(0 <= i - 1 < i);
                assert(0 <= i - 2 < i);
                assert(fibo(i as int) == fibo((i - 1) as int) + fibo((i - 2) as int));
            }
            fib.push(next_fib);
            i += 1;
        }
        fib
    }

} // verus!


// error: multiple input filenames provided (first two filenames are `` and `/tmp/tmpkymk7jcg`)
// 

// Compilation Error: False, Verified: 2, Errors: 1, Verus Errors: 2
// Safe: False