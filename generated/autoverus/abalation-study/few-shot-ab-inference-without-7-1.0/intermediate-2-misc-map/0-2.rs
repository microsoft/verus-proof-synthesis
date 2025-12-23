use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun2(x: &mut Vec<i32>) 
requires 
    forall |k:int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,
ensures 
    x@.len() == old(x)@.len(),
    forall |k:int| 0 <= k < x.len() ==> #[trigger] x@[k] == old(x)@[k] + 4,
{
    let mut i: usize = 0;
    let xlen: usize = x.len();
    while (i < xlen) 
        invariant
            i <= xlen,
            x.len() == xlen,
            forall |k:int| 0 <= k < old(x).len() ==> old(x)[k] <= 0x7FFF_FFFB,
            forall |j:int| 0 <= j < i ==> #[trigger] x@[j] == old(x)@[j] + 4,
    { 
        x.set(i, x[i] + 4);  
        i = i + 1;
    }  
}
}

// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2