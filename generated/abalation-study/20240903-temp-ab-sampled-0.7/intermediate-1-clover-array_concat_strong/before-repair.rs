
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
            0 <= n <= len,
            a.len() <= 100 && b.len() <= 100,
            c.len() == n,
            forall|i: int| (0 <= i && i < a.len()) ==> a[i] == a[i], // Since a is not modified in the loop
            forall|i: int| (0 <= i && i < b.len()) ==> b[i] == b[i], // Since b is not modified in the loop
            forall|i: int| (0 <= i && i < n && a.len() <= i && i < len) ==> c[i] == b[i - a.len()],
            forall|i: int| (0 <= i && i < n && i < a.len()) ==> c[i] == a[i],
            forall|i: int| (0 <= i && i < n && i >= a.len()) ==> c[i] == b[i - a.len()],
            forall|i: int| 0 <= i && i < n && a.len() <= i && i < len ==> c[i] == b[i - a.len()],
            forall|i: int| 0 <= i && i < n && i < a.len() ==> c[i] == a[i],
            n <= len,
            a.len() <= 100 && b.len() <= 100,
            a.len() == a.len(),
            b.len() == b.len(),
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