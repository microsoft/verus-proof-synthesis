
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

    let init_filtered_seq = Seq::empty();
    
    while (i < xlen)
        invariant
            i <= x.len(),
            y.len() <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k: u64| k % 3 == 0),
            init_filtered_seq.len() == y.len(),
            forall |j: int| 0 <= j < y.len() ==> y[j] == init_filtered_seq[j],
    { 
        if (x[i] % 3 == 0) {
            y.push(x[i]);            
        }
        i = i + 1;
    }
}
}

// is safe: False
// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 1