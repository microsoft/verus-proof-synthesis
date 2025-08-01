

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
    let x_len = x.len(); // Save the length to maintain loop isolation
    let mut max_value = x[0];  
    let mut i: usize = 1;

    while (i < x_len) 
        invariant 
            x_len == x.len(), // Ensure the length hasn't changed
            i <= x_len,      // Ensure i is within bounds
            max_value >= x[i - 1],  // Every loop has a new maximum
    {

        if x[i] > max_value { 
            max_value = x[i]; 
        }  
        i = i + 1;
    }  
    max_value  
}
}
// is safe: False
// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 2