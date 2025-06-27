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
            1 <= xlen,
            x.len() == xlen,
            i <= xlen,
            max_value >= x[0],
            // max_value should be the maximum of x[0..i]
            forall |j:int| 0 <= j < i ==> max_value >= x[j],
            // Invariant from function post-condition
            exists |k:int| 0 <= k < i && max_value == x[k],
    {  
        if x[i] > max_value { max_value = x[i]; }  
        i = i + 1;
    }  
    max_value  
}
}

// Score: (2, 0)
// Safe: True