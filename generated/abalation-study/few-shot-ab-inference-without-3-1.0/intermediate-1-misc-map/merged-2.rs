use vstd::prelude::*;
fn main() {}
verus! {

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
            forall|k: int| 0 <= k < i ==> # [trigger] x@[k] == old(x)@[k] + 4,
            forall|k: int| 0 <= k < xlen ==> old(x)[k] <= 0x7FFF_FFFB,
            forall|k: int| i <= k < xlen ==> old(x)[k] <= 0x7FFF_FFFB,
            forall|k: int| 0 <= k < i ==> x@[k] == old(x)@[k] + 4,
            forall|k: int| i <= k < xlen ==> x@[k] <= 0x7FFF_FFFB + 4,
            i <= xlen,
            x.len() == xlen,
    {
        x.set(i, x[i] + 4);
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 3