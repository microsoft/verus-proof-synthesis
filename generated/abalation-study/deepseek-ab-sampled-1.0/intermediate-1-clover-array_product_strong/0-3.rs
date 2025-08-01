
use vstd::prelude::*;
use vstd::vec::Vec;

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

    // Initialization invariant: c is empty with capacity a.len()
    assert(c.len() == 0);
    assert(c.capacity() == a.len());

    while n != len
        invariant
            /* Kilter invariants */
            n <= len,
            c.len() == n,
            c.capacity() == len,
            /* Elements added to c are the correct products */
            forall|i: int| 0 <= i < n ==> c[i] == a[i] * b[i],
    {
        {
            // Bounds invariant: n is less than a.len()
            assert(n < len);
        }

        {
            // Maintain the correct product calculation
            let product = a[n] * b[n];
            assert(c.len() == n);
            c.push(product);
            assert(c.len() == n + 1);
        }

        n = n + 1;
    }

    c
}

} // verus!

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1