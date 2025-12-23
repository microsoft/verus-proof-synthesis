

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
            // The loop variable `n` is within the bounds [0, len]
            n <= len,
            // Ensure that `a` and `b` have the same length, as required
            a.len() == b.len(),
            // Ensure that the length of `a` is within the required limit
            0 <= len <= 100,
            // The length of `c` is equal to the current value of `n`
            c.len() == n,
            // For all indices `i` less than `n`, `c[i]` is the product of `a[i]` and `b[i]`
            forall|i: int| 0 <= i < n ==> c[i] == a[i] * b[i]
    {
        let product: u32 = a[n] * b[n];
        c.push(product);
        n = n + 1;
    }
    c
}

}
// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 4