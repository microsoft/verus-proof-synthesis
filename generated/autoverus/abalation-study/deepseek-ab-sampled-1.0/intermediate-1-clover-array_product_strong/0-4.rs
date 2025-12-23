

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
            n <= len,
            0 <= len < 100,
            a.len() == b.len() == len,
            c@.len() == n,
            forall|k: int| (0 <= k < n ==> a[k] * b[k] < 1000) ==> c[k] == a[k] * b[k],
        proof {
            // Initial step: n = 0, c is empty
            if n < 1 {
                assert(c@.len() == 0);
                assert(forall|k: int| (0 <= k < 0) ==> false);
            }
            // Inductive step: assume n + 1, prove n + 2
            else {
                // Similar to the initial step, with `n` being incremented
            }
        }
    {
        let product: u32 = a[n] * b[n];
        c.push(product);
        n = n + 1;
    }
    c
}

}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1