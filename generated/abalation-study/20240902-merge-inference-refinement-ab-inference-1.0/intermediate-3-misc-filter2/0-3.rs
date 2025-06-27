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
            old(y).len() == 0,
            y.len() <= i, // y can grow to at most size i
            y.len() <= xlen,
            forall |k:int| 0 <= k < y.len() ==> y@[k] == x@.filter(|k:u64| k%3 == 0)[k], 
            // y contains elements in x that are divisible by 3, in the same order
    { 
        if (x[i] % 3 == 0) {
            y.push(x[i]);            
        }
        i = i + 1;
    }
}
}
// is safe: True
// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 4