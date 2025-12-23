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
            y.len() <= i, // y can only have as many elements as we have checked in x
            forall |j: int| 0 <= j < i ==> x.index(j) % 3 != 0 ==> !y.contains(x.index(j)), // y contains only elements divisible by 3
            forall |j: int| 0 <= j < i ==> x.index(j) % 3 == 0 ==> y@.contains(x.index(j)), // all x[j] divisible by 3 are present in y
            old(y).len() == 0, // y was empty initially
    { 
        if (x[i] % 3 == 0) {
            y.push(x[i]);            
        }
        i = i + 1;
    }
}
}

// is safe: True
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 4