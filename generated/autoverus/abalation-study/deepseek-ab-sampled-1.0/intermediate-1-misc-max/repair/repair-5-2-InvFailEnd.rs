
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
    let mut i: usize = 1;
    let xlen: usize = x.len();
    while (i < xlen)
        invariant
            xlen == x.len(),
            1 <= i <= xlen,
            exists|k: int| 0 <= k < i as int ==> max_value == x[k],
            forall|k: int| 0 <= k < i as int ==> max_value >= x[k],
    {
        if x[i] > max_value {
            max_value = x[i];
            // Add assertion to ensure the invariant holds after each swap
            proof {
                let x_ghost = x@;
                assert(exists|k: int| 0 <= k < i as int ==> max_value == x_ghost[k]);
            }
        }
        i = i + 1;
    }
    max_value
}
}


//             exists|k: int| 0 <= k < i as int ==> max_value == x[k],
//   None: exists|k: int| 0 <= k < i as int ==> max_value == x[k]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: True