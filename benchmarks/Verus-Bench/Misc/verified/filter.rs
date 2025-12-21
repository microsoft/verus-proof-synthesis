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
    
    assert(y@ == x@.take(0).filter(|k:u64| k%3 ==0)); //added in response to not-satisfied before loop error
    while (i < xlen) 
        invariant 
            0 <= i <= xlen,
            x@.len() == xlen,  // always specify the length of vectors used in the loop
            y@ == x@.take(i as int).filter(|k:u64| k%3 == 0),//routine for filter
    { 
        if (x[i] % 3 == 0) {
            y.push(x[i]);
            
        }
        assert(x@.take((i + 1) as int).drop_last() == x@.take(i as int));//routine for take, filter
        reveal(Seq::filter);//routine for filter
        i = i + 1;
    }
    assert(x@ == x@.take(x.len() as int)); //routine for take
}
}
