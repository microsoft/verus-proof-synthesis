use vstd::prelude::*;
fn main() {}
verus! {

fn product(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == # [trigger] a[i] * # [trigger] b[i],
{
    let mut c = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();
    while n != len
        invariant
            0 <= n <= a.len(),
            0 <= n <= len,
            a.len() <= 100,
            a.len() == b.len(),
            c.len() <= 100,
            c.len() == a.len(),
            c.len() == b.len(),
            c.len() == n,
            forall|i: int| (0 <= i && i < n) ==> c[i] == a[i] * b[i],
            forall|i: int| (n <= i && i < len) ==> a[i] * b[i] < 1000,
            n <= 100,
            n <= a.len(),
    {
        let product: u32 = a[n] * b[n];
        c.push(product);
        n = n + 1;
    }
    c
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 8