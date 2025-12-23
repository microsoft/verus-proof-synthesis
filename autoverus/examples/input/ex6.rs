
use vstd::prelude::*;
fn main() {}

verus!{

    pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
        requires
            old(y).len() == 0,
        ensures
            y@ == x@.filter(|k: u64| true),
    {

        let mut i: usize = 0;

        while (i < x.len())
        {

            y.push(x[i]);
            i = i + 1;
        }

    }
}
