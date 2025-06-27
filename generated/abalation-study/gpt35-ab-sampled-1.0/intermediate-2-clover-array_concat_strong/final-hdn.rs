
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn concat(a: &Vec<u64>, b: &Vec<u64>) -> (c: Vec<u64>)
    requires
        a.len() <= 100 && b.len() <= 100,
    ensures
        c@.len() == a@.len() + b@.len(),
        forall |i: int| (0 <= i && i < a.len()) ==> c[i] == a[i],
        forall |i: int| (a.len() <= i && i < c.len()) ==> c[i] == b[i - a.len()],
{
    let mut c = Vec::with_capacity(a.len() + b.len());
    let mut n: usize = 0;
    let len: usize = a.len() + b.len();
    proof {
    }
    while n != len
        invariant
            n <= len,
            a.len() <= 100,
            b.len() <= 100,
            c.len() == n,
            forall|i: int| (a.len() <= i && i < n) ==> (c[i] == b[i - a.len()]),
        {
        c.push(
            if 0 <= n && n < a.len() {
                a[n]
            } else {
                b[n - a.len()]
            },
        );
        n = n + 1;
        proof {
        }
    }
    c
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 1