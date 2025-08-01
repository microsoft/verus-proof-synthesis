
use vstd::prelude::*;

fn main() {}
verus! {

proof fn lemma_vec_capacity_concat(a: &Vec<u64>, b: &Vec<u64>, c: &Vec<u64>)
    requires
        a.len() <= 100 && b.len() <= 100,
    ensures
        old(c).len() == a.len() + b.len(),
{
    assert!(c.len() == a.len() + b.len());
}

pub fn concat(a: &Vec<u64>, b: &Vec<u64>) -> (c: Vec<u64>)
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

    lemma_vec_capacity_concat(a, b, &c);

    while n != len
        invariant
            c.len() == a.len() + b.len(),
            forall|i: int| (0 <= i && i < n) ==> 
                (c[i] == a[i] && (0 <= i && i < a.len()) || c[i] == b[i - a.len()] && (a.len() <= i && i < c.len())),
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

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1