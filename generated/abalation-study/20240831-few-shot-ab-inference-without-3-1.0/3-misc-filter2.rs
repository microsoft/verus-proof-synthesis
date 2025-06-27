
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    requires
        old(y).len() == 0,
    ensures
        y@ == x@.filter(|k: u64| k % 3 == 0),
{
    let mut i: usize = 0;
    let xlen = x.len();
    while (i < xlen)
        invariant
            i <= xlen,
            old(y).len() == 0,
            y@ == x@.subrange(0, (i) as int).filter(|k: u64| k % 3 == 0),
            forall |k: int| 0 <= k < y.len() ==> y[k] % 3 == 0, // Invariant for array `y` since it's not modified by `y.set()` within the loop
    {
        if (x[i] % 3 == 0) {
            y.push(x[i]);
        }
        i = i + 1;
    }
}

} // verus!
// Score: (0, 2)
// Safe: True