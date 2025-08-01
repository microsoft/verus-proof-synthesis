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
    assert(x.len() >= 1);
    let mut max_value = x[0];
    let mut i: usize = 1;
    let xlen: usize = x.len();
    while (i < xlen)
        invariant
            forall|j: int| 0 <= j < i as int ==> max_value >= x[j as int],
            forall|j: int| 0 <= j < i ==> x[j] <= max_value,
            i <= xlen,
            x.len() == xlen,
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


// Score: Compilation Error: False, Verified: 1, Errors: 1, Verus Errors: 1