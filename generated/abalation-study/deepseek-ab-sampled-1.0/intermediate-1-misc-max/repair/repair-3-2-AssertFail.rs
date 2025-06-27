
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
            forall|k: int| 0 <= k < i as int ==> max_value >= x[k],
            exists|k: int| 0 <= k < i as int ==> max_value == x[k],
    {
        if x[i] > max_value {
            max_value = x[i];
            // Ensure that max_value is present in the array up to index i
            proof {
                assert(exists|k: int| 0 <= k < (i as int) + 1 ==> max_value == x[k]);
            }
        }
        i = i + 1;
    }
    proof {
        // Ensure that max_value (at least set to x[0]) is present in the array
        assert(exists|i: int| 0 <= i < x.len() as int && max_value == x[i]);
    }
    max_value
}
}


//         assert(exists|i: int| 0 <= i < x.len() as int && max_value == x[i]);
//   assertion failed: exists|i: int| 0 <= i < x.len() as int && max_value == x[i]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: True