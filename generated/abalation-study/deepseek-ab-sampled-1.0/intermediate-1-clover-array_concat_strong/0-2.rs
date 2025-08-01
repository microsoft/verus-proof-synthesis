

use vstd::prelude::*;

fn main() {}
verus! {

fn concat(a: &Vec<u64>, b: &Vec<u64>) -> (c: Vec<u64>)
    requires
        a.len() <= 100 && b.len() <= 100,
    ensures
        c@.len() == a@.len() + b@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i],
        forall|i: int| (a.len() <= i && i < c.len()) ==> c[i] == b[i - a.len()],
{
    let mut c = Vec::with_capacity(a.len() + b.len());
    let mut n: usize = 0;
    let len: usize = a.len() + b.len();

    assert(c@.len() == 0); // Initial state of c is empty

    while n != len {
        c.push(
            if 0 <= n && n < a.len() {
                a[n]
            } else {
                b[n - a.len()]
            },
        );
        proof {
            // Ensure previous state is consistent
            assert(c@.len() == n);
        }

        n = n + 1;
        proof {
            // Invariant after operation
            assert(c@.len() == n);
            // Ensure n is progressing towards len
            assert(n <= len);
        }
    }
    proof {
        // Final assertion
        assert(c@.len() == len);
    }
    c
}

} // verus!
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 8