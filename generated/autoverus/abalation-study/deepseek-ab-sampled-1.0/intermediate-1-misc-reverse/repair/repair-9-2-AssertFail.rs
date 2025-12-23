
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let mut n: usize = 0;
    let length_ghost = length as int;
    let mid = (length_ghost + ( 1 ) as int) / ( 2 ) as int; // Ensure mid covers the entire range correctly
    
    while n < length / 2
        invariant
            n <= length,
            length == old(v).len(),
            v.len() == length,
            // Strengthened invariant to cover both elements in the pair
            forall|j: int| 0 <= j < n as int 
            ==> 
                v[j] == old(v)[length_ghost - j - 1] 
                && v[length_ghost - j - 1] == old(v)[j]
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
        n += 1;
    }
    
    proof {
        assert(forall|k: int| 0 <= k < mid ==> 
                   v[k] == old(v)[length_ghost - k - 1] 
                   && v[length_ghost - k - 1] == old(v)[k]) by {
            // After the loop, this holds for all k < mid
        };
        
        assert(forall|k: int| 0 <= k < length_ghost ==> 
                   v[k] == old(v)[length_ghost - k - 1]) by {
            // For k >= mid, the elements are either in the second half or the middle
            // Since n iterates up to length / 2, all necessary swaps have been performed
        };
    }
}
}




//         assert(forall|k: int| 0 <= k < length_ghost ==> 
//                    v[k] == old(v)[length_ghost - k - 1]) by {
//   assertion failed: forall|k: int| 0 <= k < length_ghost ==>                     v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 3
// Safe: False