
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

fn product(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == # [trigger] a[i] * # [trigger] b[i],
{
    let mut c = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();
    while n != len
        invariant
            a.len() == len,
            b.len() == len,
            c.len() == n,
            forall|i: int| (0 <= i && i < n) ==> c[i] == a[i] * b[i],
            forall|k: int| 0 <= k < a.len() ==> a[k] == a[k], // a is never changed in the loop
            forall|k: int| 0 <= k < b.len() ==> b[k] == b[k], // b is never changed in the loop
            n <= len,
            a.len() <= 100 && a.len() == b.len(),
    {
        let product: u32 = a[n] * b[n];
        assert(0 <= a[( n ) as int] * b[( n ) as int] < 1000) by (nonlinear_arith)
            requires
                a.len() <= 100 && a.len() == b.len(),
                forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000),
                0 <= n < a.len(),
                {};
        c.push(product);
        n = n + 1;
    }
    c
}

} // verus!


// Score: (2, 0)
// Safe: True