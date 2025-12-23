
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
    proof {
        assert(forall |i: int| (0 <= i && i < a.len()) ==> c[i] == a[i]);  // Added by AI
    }
    while n != len
        invariant
            a.len() <= 100,
            b.len() <= 100,
            c.len() == n,
            forall|i: int| (0 <= i && i < n) ==> (c[i] == a[i]),
            forall|i: int| (a.len() <= i && i < n) ==> (c[i] == b[i - a.len()]),
            n <= len,
            a.len() <= 100,  // added loop invariant
            b.len() <= 100,  // added loop invariant
            forall |i: int| (0 <= i && i < a.len()) ==> c[i] == a[i],  // Added by AI
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


//             forall |i: int| (0 <= i && i < a.len()) ==> c[i] == a[i],  // Added by AI
//   None: forall |i: int| (0 <= i && i < a.len()) ==> c[i] == a[i]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: True