
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

// Lemma to show the monotonicity of fibo function
proof fn lemma_monotonic_fibo(i: int, j: int)
    requires
        0 <= i <= j,
    ensures
        fibo(i) <= fibo(j),
    decreases j - i
{
    if i < j {
        lemma_monotonic_fibo(i, j - 1);
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
        let fib_i_minus_1 = fib[i - 1];
        let fib_i_minus_2 = fib[i - 2];

        assert(fib_i_minus_1 as int + fib_i_minus_2 as int <= 0x7FFF_FFFF) by {
            lemma_monotonic_fibo((i - 2) as int, (i as int).saturating_sub(2));
            lemma_monotonic_fibo((i - 1) as int, (i as int).saturating_sub(1));
            assert(fibo((i - 2) as int) <= 0x7FFF_FFFF && fibo((i - 1) as int) <= 0x7FFF_FFFF);
        };

        let next_fib = fib_i_minus_1 + fib_i_minus_2;
        fib.push(next_fib);
        i += 1;
    }
    fib
}

} // verus!


//         let next_fib = fib[i - 1] + fib[i - 2];
//   None: fib[i - 1] + fib[i - 2]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False