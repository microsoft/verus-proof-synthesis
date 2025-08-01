
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]

pub fn myfun1(x: &Vec<u64>) -> (res: u64)
    requires
        x.len() >= 1,
    ensures
        forall|i: int| 0 <= i < x.len() ==> res >= x[i],
        exists|i: int| 0 <= i < x.len() && res == x[i],
{
    assert(x.len() >= 1);
    let mut max_value = x[0];
    let mut i: usize = 0;
    let xlen: usize = x.len();
    while (i < xlen - 1)
        invariant
            xlen == x.len(),
            0 <= i <= xlen,
            exists|k: int| 0 <= k < i as int ==> max_value == x[k],
            forall|k: int| 0 <= k < i as int ==> max_value >= x[k],
    {
        i += 1;
        if x[i] > max_value {
            max_value = x[i];
        }
    }
    max_value
}
}


//             exists|k: int| 0 <= k < i as int ==> max_value == x[k],
//   None: exists|k: int| 0 <= k < i as int ==> max_value == x[k]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 3
// Safe: False