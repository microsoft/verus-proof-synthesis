
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
            x.len() == xlen,
            y.len() <= i,
            y.len() <= xlen,
            x.len() == xlen, // Length invariant for x
            y.len() <= xlen, // Length invariant for y
            y@ == x@.subrange(0, (i) as int).filter(|k: u64| k % 3 == 0),
            old(y).len() == 0,
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