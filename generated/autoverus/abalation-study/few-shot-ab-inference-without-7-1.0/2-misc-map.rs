
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn myfun2(x: &mut Vec<i32>)
    requires
        forall|k: int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,
    ensures
        x@.len() == old(x)@.len(),
        forall|k: int| 0 <= k < x.len() ==> # [trigger] x@[k] == old(x)@[k] + 4,
{
    let mut i: usize = 0;
    let xlen: usize = x.len();
    while (i < xlen)
        invariant
            forall|j: int| 0 <= j < i ==> # [trigger] x@[j] == old(x)@[j] + 4,
            forall|k: int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,
            i <= xlen,
            x.len() == xlen,
            forall|k: int| 0 <= k < x.len() ==> old(x)[k] <= 0x7FFF_FFFB, // Updated invariant to cover every element in the array.
            x.len() == xlen,
    {
        x.set(i, x[i] + 4);
        i = i + 1;
    }
}

} // verus!
// Score: (0, 2)
// Safe: True