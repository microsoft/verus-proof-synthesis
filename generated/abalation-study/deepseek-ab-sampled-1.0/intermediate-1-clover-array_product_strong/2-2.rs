
use vstd::prelude::*;

fn main() {}

verus! {

fn product(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i] * b[i],
{
    let mut c = Vec::with_capacity(a.len());
    let mut n: usize = 0;
    let len: usize = a.len();
    while (n != len)
        invariant 
            n <= len,
            a.len() == len,
            b.len() == len,
            c.len() == n,
            forall |k: int| (0 <= k < n as int) ==> c[k as int] == a[k as int] * b[k as int],
    {
        let product: u32 = a[n] * b[n];
        c.push(product);
        n += 1;
    }
    c
}

} // verus!




// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2