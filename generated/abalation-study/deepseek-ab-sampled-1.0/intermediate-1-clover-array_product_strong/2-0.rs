
use vstd::prelude::*;

fn main() {}
verus! {

fn product(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == #[trigger] a[i] * #[trigger] b[i],
{
    let mut c = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();
    
    while (n != len)
        invariant 
            // Read variables: a, b, len, n
            a.len() == b.len(),
            n <= len,
            n <= c.len(),
            // Invariants for a and b
            a.len() <= 100,
            forall|i: int| (0 <= i && i < len) ==> (a[i] * b[i] < 1000),
            // Correctness invariant for 'c'
            c.len() == n,
            forall|i: int| (0 <= i && i < len) 
                ==> (if i < n then c[i] == a[i] * b[i] else true)
    {
        let product: u32 = a[n] * b[n];
        c.push(product);
        n = n + 1;
    }

    c
}
} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1