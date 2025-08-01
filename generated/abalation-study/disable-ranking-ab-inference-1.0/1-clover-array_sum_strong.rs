use vstd::prelude::*;

fn main() {}
verus! {

fn sum(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] + b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == #[trigger] a[i] + #[trigger] b[i],
{
    let mut c = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();
    while n != len
        invariant
            // Invariants about the loop index and lengths
            n <= len,
            len == a.len(),
            len == b.len(),
            c.len() == n,
            // Invariants about the contents
            forall|i: int| (0 <= i && i < n) ==> c[i] == a[i] + b[i],
            // Invariants about unchanged conditions
            a.len() <= 100 && a.len() == b.len(),
            forall|i: int| (0 <= i && i < a.len()) ==> (a[i] + b[i] < 1000),
    {
        let sum: u32 = a[n] + b[n];
        c.push(sum);
        n = n + 1;
    }
    c
}

} // verus!
// Score: (2, 0)
// Safe: True