use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    requires
        old(y).len() == 0,
    ensures
        y@ == x@.filter(|k: u64| k % 3 == 0),
{
    let mut i: usize = 0;
    let xlen = x.len();
    while (i < xlen)
        invariant
            forall|j: int|
                0 <= j < i ==> (x[j] % 3 != 0 || exists|k: int| 0 <= k < y.len() && y[k] == x[j]),
            forall|j: int| 0 <= j < y.len() ==> y[j] % 3 == 0,
            i <= xlen,
            old(y).len() == 0,
            y.len() <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k: u64| k % 3 == 0),
    {
        if (x[i] % 3 == 0) {
            y.push(x[i]);
        }
        i = i + 1;
    }
}

} // verus!


// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 7