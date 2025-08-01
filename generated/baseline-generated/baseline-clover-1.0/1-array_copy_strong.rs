use vstd::prelude::*;

fn main() {}
verus! {

fn copy(a: &Vec<u64>) -> (b: Vec<u64>)
    requires
        a.len() <= 100,
    ensures
        b@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> b[i] == a[i],
{
    let mut b = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();
    while n != len
        invariant
            0 <= n <= len,
            b@.len() == n as int,
            forall|i: int| (0 <= i && i < n) ==> b[i] == a[i],
            a@.len() == len as int,
    {
        b.push(a[n]);
        n = n + 1;
    }
    b
}

} // verus!
// Score: (2, 0)
// Safe: True