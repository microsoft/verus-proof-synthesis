

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
            x.len() == xlen,
            max_value == x[i-1] || max_value >= x[i-1],
            0 < i <= xlen,
            i < x.len() + 1,
            forall |k:int| 0 <= k < i ==> max_value >= x[k],
        {
            if x[i] > max_value { max_value = x[i]; }  
            i = i + 1;
        }
    max_value  
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1