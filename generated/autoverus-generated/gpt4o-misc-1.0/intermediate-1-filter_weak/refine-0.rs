
use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    requires
        old(y).len() == 0,
    ensures
        forall|k: int| 0 <= k < y.len() ==> y[k] % 3 == 0 && x@.contains(y@[k]),
{
    let mut i: usize = 0;
    let xlen = x.len();
    while (i < xlen)
        invariant
            forall|j: int| 0 <= j < y.len() ==> y[j] % 3 == 0 && x@.contains(y@[j]),
            i <= xlen,
            y.len() <= i,
            y.len() <= xlen,
            old(y).len() == 0,
    {
        if (x[i] % 3 == 0) {
            y.push(x[i]);
        }
        i = i + 1;
    }
}

} // verus!
