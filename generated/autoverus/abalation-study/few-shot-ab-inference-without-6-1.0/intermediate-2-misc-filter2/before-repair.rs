
use vstd::prelude::*;
fn main() {}
verus! {

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
            y.len() <= i,
            y.len() <= xlen,
            y@ == x@.subrange(0, (i) as int).filter(|k: u64| k % 3 == 0),
            old(y).len() == 0,
            x.len() == xlen,
            forall |k:int| 0 <= k < x.len() ==> x[k] == x[k], // x is never changed in this loop
    {
        if (x[i] % 3 == 0) {
            y.push(x[i]);
        }
        i = i + 1;
    }
}

} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 3