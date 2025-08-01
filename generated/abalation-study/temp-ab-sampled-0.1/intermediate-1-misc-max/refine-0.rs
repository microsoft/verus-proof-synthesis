
use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun1(x: &Vec<u64>) -> (res: u64)
    requires
        x.len() >= 1,
    ensures
        forall|i: int| 0 <= i < x.len() ==> res >= x[i],
        exists|i: int| 0 <= i < x.len() && res == x[i],
{
    let mut max_value = x[0];
    let mut i: usize = 1;
    let xlen: usize = x.len();
    while (i < xlen)
        invariant
            1 <= xlen,
            exists|j: int| 0 <= j < i && max_value == x[j],
            forall|j: int| 0 <= j < i ==> max_value >= x[j],
            i <= xlen,
            x.len() >= 1,
    {
        if x[i] > max_value {
            max_value = x[i];
        }
        i = i + 1;
    }
    max_value
}

} // verus!
