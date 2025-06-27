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
            y.len() <= xlen,
            old(y).len() == 0,
            forall |k:int| 0 <= k < i ==> (if x[k] % 3 == 0 { y.contains(&x[k]) } else { true }),
            forall |k:int| 0 <= k < y.len() ==> y[k] % 3 == 0,            
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