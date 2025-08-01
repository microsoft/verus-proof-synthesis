
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

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
    while n != len
        invariant
            a.len() == a.len(),
            b.len() == b.len(),
            c.len() == n,
            forall|i: int| (0 <= i && i < n && i < a.len()) ==> c[i] == a[i],
            forall|i: int| (a.len() <= i && i < n && i < len) ==> c[i] == b[i - a.len()],
            forall|k: int| 0 <= k < a.len() ==> a[k] == a[k], // Added to cover all elements of array a
            forall|k: int| 0 <= k < b.len() ==> b[k] == b[k], // Added to cover all elements of array b
            n <= len,
            a.len() <= 100, // Repeating the upper bound invariant
            b.len() <= 100, // Repeating the upper bound invariant
    {
        c.push(
            if 0 <= n && n < a.len() {
                a[n]
            } else {
                b[n - a.len()]
            },
        );
        n = n + 1;
    }
    c
}

} // verus!
// Score: (1, 0)
// Safe: True