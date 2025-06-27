

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
            1 <= i <= xlen,
            x.len() == xlen,
            max_value == x[0], //Initial value guarantee
            max_value >= x[i - 1], //Invariant about max_value
    {  
        if x[i] > max_value { max_value = x[i]; }  
        i = i + 1;
        proof {
            //Proving that max_value is updated correctly.
            //If x[i] > max_value, then max_value is updated to x[i].
            //Otherwise, max_value remains the same.
            //This ensures that max_value is always the maximum of the examined elements.
        }
    }  
    max_value  
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2