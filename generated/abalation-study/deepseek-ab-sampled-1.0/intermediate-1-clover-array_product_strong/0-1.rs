

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
    while n != len 
        invariant
            len <= 100,
            n <= a.len(),
            c.len() == n,
            // Ensure that all elements up to 'n' have been correctly filled
            forall|k: int| 0 <= k < n ==> c[k] == a[k] * b[k],
            // Ensure that the product for each element is within the constraint
            forall|k: int| 0 <= k < a.len() ==> (a[k] * b[k] < 1000),
    {
        let product: u32 = a[n] * b[n];
        c.push(product);
        n = n + 1;
    }
    c
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 5