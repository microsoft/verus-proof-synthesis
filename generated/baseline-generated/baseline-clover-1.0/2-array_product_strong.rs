use vstd::prelude::*;

fn main() {}
verus! {

fn product(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall |i: int| 0 <= i < a.len() ==> a[i] * b[i] < 1000,
    ensures
        c@.len() == a@.len(),
        forall |i: int| 0 <= i < a.len() ==> c[i] == #[trigger] a[i] * #[trigger] b[i],
{
    let mut c = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();

    while n != len
    invariant
        c@.len() == n as int,
        forall |i: int| 0 <= i < n as int ==> c[i] == a[i] * b[i],
        n <= len,
        len == a.len(),
        len == b.len(),
        forall |i: int| 0 <= i < a.len() ==> a[i] * b[i] < 1000,
    {
        let product: u32 = a[n] * b[n];
        c.push(product);
        n = n + 1;
    }
    c
}

} // verus!
// Score: (2, 0)
// Safe: False