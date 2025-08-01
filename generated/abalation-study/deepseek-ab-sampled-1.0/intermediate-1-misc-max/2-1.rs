

use vstd::prelude::*;
fn main() {}

verus!{

pub fn myfun1(x: &Vec<u64>) -> (res: u64) 
    requires 
        x.len() >= 1,
    ensures
        forall |i:int| 0 <= i < x.len() ==> res >= x[i],
        exists |i:int| 0 <= i < x.len() && res == x[i],
{
    let mut max_value = x[0];  
    let mut i: usize = 1;
    let xlen: usize = x.len();
    while (i < xlen)
        invariant
            i <= xlen,
            x.len() == xlen,
            0 < xlen,
            max_value == x[0], // since we have loop invariant here, perhaps better to show that max_value remains the maximum so far.
            forall |j: int| 0 <= j < i ==> max_value == x@.subrange(0, i as int).max(),
    {  
        if x[i] > max_value { 
            max_value = x[i]; 
        }  
        i = i + 1;
    }  
    max_value  
}
}
// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1