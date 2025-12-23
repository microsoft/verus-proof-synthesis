
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
    
    // Track both the maximum value and its index
    let mut max_value = x[0];
    let mut max_index = 0;
    let mut i: usize = 1;
    let xlen: usize = x.len();
    
    while (i < xlen)
        // Update invariants to include max_index and its properties
        invariant
            xlen == x.len(),
            1 <= i <= xlen,
            max_index < xlen,
            forall|k: int| 0 <= k < i as int ==> max_value >= x[k],
            exists|k: int| 0 <= k < i as int ==> max_value == x[k],
    {
        if x[i] > max_value {
            max_value = x[i];
            max_index = i; // Update the index of the maximum value
        }
        i += 1;
    }
    
    // Update the proof block to use the tracked index
    proof {
        assert(max_index < x.len() as int);
        assert(0 <= max_index < x.len() as int);
        assert(max_value == x[( max_index ) as int]);
        assert(exists|i: int| 0 <= i < x.len() as int && max_value == x[i]);
    }
    
    max_value
}

}



//         assert(exists|i: int| 0 <= i < x.len() as int && max_value == x[i]);
//   assertion failed: exists|i: int| 0 <= i < x.len() as int && max_value == x[i]

// Compilation Error: False, Verified: 0, Errors: 1, Verus Errors: 2
// Safe: False