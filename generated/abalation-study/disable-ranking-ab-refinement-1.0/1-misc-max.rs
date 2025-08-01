
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
            0 <= i <= xlen,
            exists|j: int| 0 <= j < i && max_value == x[j],
            forall|j: int| 0 <= j < i ==> max_value >= x[j],
            max_value >= x[0],
            x.len() == xlen,
    {
        if x[i] > max_value {
            max_value = x[i];
        }
        i = i + 1;
    }
    max_value
}

} // verus!

// Score: (2, 0)
// Safe: True