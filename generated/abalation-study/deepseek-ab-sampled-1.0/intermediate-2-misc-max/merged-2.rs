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
            0 < i <= xlen,
            1 <= i <= xlen,
            forall|k: int| 0 <= k < i ==> max_value >= x[k],
            i < x.len() + 1,
            exists|j: int| 0 <= j < i && max_value == x[j],
            forall|j: int| 0 <= j < i ==> max_value >= x[j],
            i <= xlen,
            max_value == x[0],
            max_value == x[i - 1] || max_value >= x[i - 1],
            max_value >= x[i - 1],
            x.len() == xlen,
            max_value >= x[0],
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