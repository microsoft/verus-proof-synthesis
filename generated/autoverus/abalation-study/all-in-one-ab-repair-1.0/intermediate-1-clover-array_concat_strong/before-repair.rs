
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
    while n != len
        invariant
            a.len() <= 100 && b.len() <= 100,
            c.len() == n,
            c@.len() == n,
            // The array 'a' is not modified in the loop
            forall|k: int| 0 <= k < a.len() ==> a[k] == a[k],
            // The array 'b' is not modified in the loop
            forall|k: int| 0 <= k < b.len() ==> b[k] == b[k],
            forall|i: int| (0 <= i && i < n && !(i < a.len())) ==> c[i] == b[i - a.len()],
            forall|i: int| (0 <= i && i < n && i < a.len()) ==> c[i] == a[i],
            n <= len,
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

// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1