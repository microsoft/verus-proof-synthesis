
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
    let mut max_index = 0; // Track the index of max_value
    let len = x.len();
    let mut i: usize = 1;
    while (i < len) 
        invariant
            len == x.len(),
            max_index <= i,
            i <= len,
            forall|k: int| 0 <= k < i as int ==> x[k] <= max_value,
    {
        if x[i] > max_value {
            max_value = x[i];
            max_index = i; // Update the index when max_value is updated
        }
        i += 1;
    }
    proof {
        // The max_value is at least x[0]
        let first_max = if max_index == 0 {
            0
        } else {
            max_index as int
        };
        assert(exists|k: int| 0 <= k < len ==> max_value == x[k as int]);
        // Since max_value is updated based on x, it must be present
    }
    max_value
}

}



//         assert(exists|i: int| 0 <= i < x.len() as int && max_value == x[i]);
//   assertion failed: exists|i: int| 0 <= i < x.len() as int && max_value == x[i]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: False