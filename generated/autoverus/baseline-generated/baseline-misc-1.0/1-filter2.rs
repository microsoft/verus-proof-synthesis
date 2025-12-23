use vstd::prelude::*;
fn main() {}

verus!{
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k % 3 == 0),
{
    let mut i: usize = 0;
    let xlen = x.len();
    
    assert(y@ == x@.take(0).filter(|k:u64| k % 3 == 0)); // Initial state
    while (i < xlen)
        invariant
            0 <= i <= xlen,
            x@.len() == xlen,
            y@ == x@.take(i as int).filter(|k:u64| k % 3 == 0),
    { 
        if (x[i] % 3 == 0) {
            y.push(x[i]);            
        }
        assert(x@.take((i + 1) as int).drop_last() == x@.take(i as int));
        reveal(Seq::filter);
        i = i + 1;
    }

    assert(x@ == x@.take(x.len() as int));
}
}
// Score: (2, 0)
// Safe: True