

use vstd::prelude::*;

fn main() {}
verus! {

fn product(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i] * b[i],
    // Add loop invariants here

    // Begin Implementation
    {
        let mut c = Vec::with_capacity(a.len());
        let mut n: usize = 0;
        let len: usize = a.len();

        // Invariant for the initialization loop
        while n != len
            invariant
                n <= len,
                c.len() == n,
                a.len() == b.len(),
                a.len() <= 100,
        {
            let product: u32 = a[n] * b[n];
            c.push(product);
            n = n + 1;
        }

        c
    }
    // End Implementation

    // Add proof here if necessary

} // verus!
// is safe: False
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 4