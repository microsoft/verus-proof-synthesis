

use vstd::prelude::*;

fn main() {}

verus! {

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
            max_value >= x@[0, i as int],
            exists |j:int| 0 <= j < i as int && max_value == x[j],
    {  
        if x[i] > max_value { max_value = x[i]; }  
        i = i + 1;
    }  
    max_value  
}
}
// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1