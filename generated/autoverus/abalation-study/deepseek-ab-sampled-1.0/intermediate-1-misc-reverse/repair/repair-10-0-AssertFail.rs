
use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

proof fn test_exists_succeeds() {
    proof {
        assert(is_even(4));
    }
    assert(exists|i: int| #[trigger] is_even(i));
}
}


//         assert(forall|k: int| 0 <= k < length_ghost ==> 
//                    v[k] == old(v)[length_ghost - k - 1]) by {
//   assertion failed: forall|k: int| 0 <= k < length_ghost ==>                     v[k] == old(v)[length_ghost - k - 1]

// Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 2
// Safe: False