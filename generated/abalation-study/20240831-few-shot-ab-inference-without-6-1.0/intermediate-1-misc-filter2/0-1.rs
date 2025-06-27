use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k%3 == 0),
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    while (i < xlen) 
        invariant
            i <= xlen,
            x.len() == xlen,
            old(y).len() == 0,
            y.len() <= xlen,
            forall |k: int| 0 <= k < i ==> !(x[k] % 3 == 0) || (exists |j: int| 0 <= j < y.len() && y[j] == x[k]),
            forall |k: int| 0 <= k < y.len() ==> exists |j: int| 0 <= j < i && y[k] == x[j] && x[j] % 3 == 0,
    { 
        if (x[i] % 3 == 0) {
            y.push(x[i]);            
        }
        i = i + 1;
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1